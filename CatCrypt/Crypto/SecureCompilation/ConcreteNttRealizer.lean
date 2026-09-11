/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.GenericNttEmitValue
public import CatCrypt.Crypto.SecureCompilation.ConcreteNttEmitRealization
public import CatCrypt.Crypto.Optimizer.Lattice.ConcreteNttRoots
public import CatCrypt.Crypto.Optimizer.Lattice.ConcreteNttInstances

/-!
# A CONCRETE NTT realizer: round-trip-verified encoding, KAT-free realization

The generic NTT-multiply emit→value seam (`GenericNttEmitValue`) discharges the
realization down to a leaf-realization predicate that is, at the ML-KEM
parameters, an externally-checked **KAT** hypothesis (`mlkem_nttEmitRealizes_of_kernel`
takes `NttKernelRealizes … leafSpec` as an assumption — "the emitted kernel's
leaf bytes decode to the cyclic convolution").  Its non-vacuity witnesses
(`nttKernelRealizes_canonical`, `mlkem_nttKernelRealizes_canonical`) exhibit a
concrete `LeafSpec` that satisfies the predicate, but only **parametrically** over
an abstract `encode`/`decode` pair with a *hypothesised* section
(`hsection : ∀ p, decode (encode p) = p`).

This module makes that section **concrete and proved**, so the realization holds
**unconditionally** for a spec-computing realizer.  We exhibit:

* a genuine `RustVal (.TPolyMod q n)` carrier (a real byte array,
  `Fin (storageBytes) → BitVec 8` — not a constructor wrapping the function and
  certainly not an `axiom`), with a concrete two-bytes-per-coefficient
  little-endian `encodeP`/`decodeP` pair, and
* a **proved** round-trip `decodeP_encodeP : ∀ x, decodeP (encodeP x) = x`
  (the crux — this is the byte-level fact a KAT would *assert*; here it is a
  theorem, valid for every coefficient vector, whenever `q < 2^16`).

From that round-trip the leaf realizer `cyclicConvLeafSpecP` provably computes the
cyclic convolution (`NttKernelRealizesP`, a theorem — no KAT), and composing with
the proven primitive-root facts (`isPrimitiveRoot_17_256`, `n_ne_zero_3329`) via
the commuting-square discharge gives the unconditional ML-KEM realization
`mlkem_nttEmitRealizes_concrete`.

## The `.TPolyMod` carrier vs the generic `.TFp` predicate

`GenericNttEmitValue`'s `NttKernelRealizes`/`NttEmitRealizes` hardcode the carrier
to `RustVal .TFp = JArray 48 = Fin 48 → BitVec 8` — 48 bytes = 384 bits.  No
round-trip `decode ∘ encode = id` can exist on that carrier for the ML-KEM vector
type `Fin 256 → ZMod 3329`: a faithful injection needs `≥ log₂(3329²⁵⁶) ≈ 3072`
bits, far above 384 (pigeonhole).  The lattice carrier `RustVal (.TPolyMod 3329 256)`
has `256 · 2 = 512` bytes = 4096 bits, which is large enough; it is the TowerType
the compiler actually uses for ML-KEM polynomials (`TPolyMod 3329 256`).  We
therefore re-state the realization predicates over `.TPolyMod q n` (a few lines)
and re-run the same commuting-square discharge (the math content
`nttMul_eq_cyclicConv'` is reused verbatim).

## HONEST scope — what this proves and what it does NOT

* **Proved (unconditional Lean theorem):** there is a *concrete* leaf realizer
  (`cyclicConvLeafSpecP`) and a *concrete*, round-trip-verified byte encoding
  (`encodeP`/`decodeP`, `decodeP_encodeP`) under which the full NTT-multiply
  realization `NttEmitRealizesP` holds for **all** inputs — strictly stronger
  than *assuming* a KAT, because the byte-level decode-equals-convolution fact is
  a theorem here, not a test vector.
* **NOT proved (the remaining residual):** that the *jasmin-emitted machine bytes*
  of the real `ntt_poly_mul_3329_256` kernel equal this realizer.  That equality
  — actual emitted assembly ≡ `cyclicConvLeafSpecP` — is the owned-machine-code
  route and is a separate follow-up.  This file removes the *encoding* KAT (the
  `decode ∘ encode = id` assumption); it does **not** remove the *machine-code*
  obligation.

## References
* NIST FIPS 203 (ML-KEM), FIPS 204 (ML-DSA)
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ConcreteNttRealizer

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.GenericNttEmitValue
open CatCrypt.Crypto.Optimizer.Lattice.NTTMultiplyCorrectGeneric
open CatCrypt.Crypto.Optimizer.Lattice.CyclicConvolutionGeneric
open CatCrypt.Crypto.Optimizer.Lattice.ConcreteNttRoots

/-! ## §1  Concrete, round-trip-verified byte encoding over `.TPolyMod q n`

`RustVal (.TPolyMod q n) = JArray (.TPolyMod q n).storageBytes`, a genuine byte
array.  For `q < 2^16` each coefficient fits in two bytes; we lay them out
little-endian, two bytes per coefficient.  The decode reads the two bytes back as
a `ZMod q`.  The round-trip is a per-coefficient `Nat`-arithmetic fact. -/

/-- Byte width per coefficient used by our concrete layout: two bytes
    (little-endian), sufficient whenever `q < 2^16`. -/
def coeffBytes : ℕ := 2

/-- The concrete carrier for a length-`n` coefficient vector mod `q`:
    `n` coefficients laid out two bytes each, little-endian.  This is a *real*
    `Fin (n * 2) → BitVec 8` byte array. -/
abbrev PolyBytes (n : ℕ) : Type := Fin (n * coeffBytes) → BitVec 8

/-- Encode a coefficient vector into `n·2` little-endian bytes: byte `2i` is the
    low byte of `(x i).val`, byte `2i+1` the high byte. -/
def encodeP {q n : ℕ} [NeZero q] (x : Fin n → ZMod q) : PolyBytes n :=
  fun b =>
    let i : ℕ := b.val / coeffBytes
    let lane : ℕ := b.val % coeffBytes
    if h : i < n then
      let v : ℕ := (x ⟨i, h⟩).val
      if lane = 0 then BitVec.ofNat 8 (v % 256) else BitVec.ofNat 8 (v / 256)
    else 0

/-- Decode `n·2` little-endian bytes back into a coefficient vector:
    `coeff i = byte(2i) + 256 · byte(2i+1)  (mod q)`. -/
def decodeP {q n : ℕ} [NeZero q] (a : PolyBytes n) : Fin n → ZMod q :=
  fun i =>
    let lo : ℕ := (a ⟨i.val * coeffBytes, by
      have hlt := i.isLt; unfold coeffBytes; omega⟩).toNat
    let hi : ℕ := (a ⟨i.val * coeffBytes + 1, by
      have hlt := i.isLt; unfold coeffBytes; omega⟩).toNat
    ((lo + 256 * hi : ℕ) : ZMod q)

/-- **The verified round-trip (the crux).**  For any modulus `q < 2^16`, decoding
    the concrete little-endian byte encoding of a coefficient vector returns the
    vector unchanged — for **all** inputs.  This is the byte-level fact a KAT would
    merely *assert*; here it is a theorem. -/
theorem decodeP_encodeP {q n : ℕ} [NeZero q] (hq : q < 65536)
    (x : Fin n → ZMod q) : decodeP (encodeP x) = x := by
  funext i
  have hval : (x i).val < 65536 := lt_of_lt_of_le (ZMod.val_lt (x i)) (le_of_lt hq)
  simp only [decodeP]
  -- The low byte: lane 0, value `(x i).val % 256`.
  have hlo : (encodeP x ⟨i.val * coeffBytes, by have := i.isLt; unfold coeffBytes; omega⟩).toNat
      = (x i).val % 256 := by
    simp only [encodeP]
    have hi' : i.val * coeffBytes / coeffBytes = i.val := by
      unfold coeffBytes; omega
    have hlane : i.val * coeffBytes % coeffBytes = 0 := by
      unfold coeffBytes; omega
    rw [hi', hlane]
    rw [dif_pos i.isLt, if_pos rfl, Fin.eta, BitVec.toNat_ofNat]
    have : (x i).val % 256 < 256 := Nat.mod_lt _ (by decide)
    omega
  -- The high byte: lane 1, value `(x i).val / 256`.
  have hhi : (encodeP x ⟨i.val * coeffBytes + 1, by have := i.isLt; unfold coeffBytes; omega⟩).toNat
      = (x i).val / 256 := by
    simp only [encodeP]
    have hi' : (i.val * coeffBytes + 1) / coeffBytes = i.val := by
      unfold coeffBytes; omega
    have hlane : (i.val * coeffBytes + 1) % coeffBytes = 1 := by
      unfold coeffBytes; omega
    rw [hi', hlane]
    rw [dif_pos i.isLt, if_neg (by decide : (1 : ℕ) ≠ 0), Fin.eta, BitVec.toNat_ofNat]
    have : (x i).val / 256 < 256 := by omega
    omega
  rw [hlo, hhi]
  have hrecon : (x i).val % 256 + 256 * ((x i).val / 256) = (x i).val := by omega
  rw [hrecon, ZMod.natCast_val, ZMod.cast_id]

/-! ## §2  Realization predicates over the `.TPolyMod q n` carrier

The generic predicates in `GenericNttEmitValue` hardcode the `.TFp` carrier (48
bytes), which is too small for an honest round-trip (see the module docstring).
We re-state the same two predicates over `RustVal (.TPolyMod q n)` — the carrier
the compiler actually uses for ML-KEM polynomials, with `512` bytes of room — and
re-run the identical commuting-square discharge.  Only the carrier TowerType
differs; the convolution math (`nttMul_eq_cyclicConv'`) is reused verbatim.

The carrier `RustVal (.TPolyMod q n) = JArray ((.TPolyMod q n).storageBytes)`
equals `PolyBytes n = JArray (n · coeffBytes)` definitionally exactly when
`(.TPolyMod q n).storageBytes = n · coeffBytes`, i.e. when `q` needs two bytes
per coefficient.  We package that fact as a hypothesis `hwidth` and cast through
it, so the predicates and the discharge stay parametric in `q, n` (the ML-KEM
literals satisfy `hwidth` by `rfl` and `ZMod 3329` is a field, discharging the
`Field` instance `nttMul_eq_cyclicConv'` needs). -/

/-- The `.TPolyMod`-carrier cyclic-convolution kernel-realization predicate: the
    leaf-call value decodes to the length-`n` cyclic convolution.  Identical in
    shape to `GenericNttEmitValue.NttKernelRealizes`, but over the genuinely
    large `.TPolyMod q n` byte carrier. -/
def NttKernelRealizesP (q n : ℕ) [NeZero q] [NeZero n]
    (decode : RustVal (.TPolyMod q n) → (Fin n → ZMod q))
    (leaf : String) (leafSpec : LeafSpec) : Prop :=
  ∀ (aVal bVal oldDest : RustVal (.TPolyMod q n)),
    decode
        (leafSpec.call leaf (.TPolyMod q n) [.TPolyMod q n, .TPolyMod q n] oldDest
          [⟨.TPolyMod q n, aVal⟩, ⟨.TPolyMod q n, bVal⟩])
      = cyclicConv n (decode aVal) (decode bVal)

/-- The `.TPolyMod`-carrier full NTT-multiply realization predicate: the leaf-call
    value decodes to `nttMul n ω …`. -/
def NttEmitRealizesP (q n : ℕ) [NeZero q] [NeZero n] [Fact (Nat.Prime q)] (ω : ZMod q)
    (decode : RustVal (.TPolyMod q n) → (Fin n → ZMod q))
    (leaf : String) (leafSpec : LeafSpec) : Prop :=
  ∀ (aVal bVal oldDest : RustVal (.TPolyMod q n)),
    decode
        (leafSpec.call leaf (.TPolyMod q n) [.TPolyMod q n, .TPolyMod q n] oldDest
          [⟨.TPolyMod q n, aVal⟩, ⟨.TPolyMod q n, bVal⟩])
      = nttMul n ω (decode aVal) (decode bVal)

/-- **Commuting-square discharge over `.TPolyMod`.**  Identical to
    `nttEmitRealizes_of_cyclicConv`, re-run on the `.TPolyMod` carrier: a primitive
    `n`-th root `ω` with `(n : ZMod q) ≠ 0` rewrites `nttMul = cyclicConv` (the
    proven `nttMul_eq_cyclicConv'`), lifting the kernel realization to the full
    NTT-multiply realization. -/
theorem nttEmitRealizesP_of_cyclicConv {q n : ℕ} [NeZero q] [NeZero n]
    [Fact (Nat.Prime q)] {ω : ZMod q}
    (decode : RustVal (.TPolyMod q n) → (Fin n → ZMod q))
    (leaf : String) (leafSpec : LeafSpec)
    (hω : IsPrimitiveRoot ω n) (hn : (n : ZMod q) ≠ 0)
    (hker : NttKernelRealizesP q n decode leaf leafSpec) :
    NttEmitRealizesP q n ω decode leaf leafSpec := by
  intro aVal bVal oldDest
  rw [hker aVal bVal oldDest, nttMul_eq_cyclicConv' hω hn]

/-! ## §3  The concrete, spec-computing realizer (no abstract section)

`cyclicConvLeafSpecP` is the canonical realizer wired to the **concrete**
`encodeP`/`decodeP` of §1: at the NTT leaf it decodes both polynomial arguments,
computes their cyclic convolution, and re-encodes; off-leaf it returns `oldDest`.
Because the round-trip `decodeP_encodeP` is a *theorem*, `NttKernelRealizesP`
holds **unconditionally** — there is no `hsection` hypothesis to assume.

`hwidth : (.TPolyMod q n).storageBytes = n * coeffBytes` makes `RustVal
(.TPolyMod q n)` equal to `PolyBytes n`, letting the byte-level `encodeP`/`decodeP`
serve as the carrier codec.  For ML-KEM (`q = 3329`, `n = 256`) it holds by
`rfl`. -/

/-- The decoder on the `.TPolyMod q n` carrier, obtained from the byte-level
    `decodeP` through the width equality `hwidth`. -/
def decodeTPoly {q n : ℕ} [NeZero q]
    (hwidth : (TowerType.TPolyMod q n).storageBytes = n * coeffBytes)
    (a : RustVal (.TPolyMod q n)) : Fin n → ZMod q :=
  decodeP (cast (congrArg CatCrypt.Crypto.Jasmin.JArray hwidth) a)

/-- The encoder on the `.TPolyMod q n` carrier, obtained from the byte-level
    `encodeP` through the width equality `hwidth`. -/
def encodeTPoly {q n : ℕ} [NeZero q]
    (hwidth : (TowerType.TPolyMod q n).storageBytes = n * coeffBytes)
    (x : Fin n → ZMod q) : RustVal (.TPolyMod q n) :=
  cast (congrArg CatCrypt.Crypto.Jasmin.JArray hwidth.symm) (encodeP x)

/-- Round-trip on the carrier: `decodeTPoly ∘ encodeTPoly = id`, inherited from
    `decodeP_encodeP` by transporting along `hwidth`. -/
theorem decodeTPoly_encodeTPoly {q n : ℕ} [NeZero q] (hq : q < 65536)
    (hwidth : (TowerType.TPolyMod q n).storageBytes = n * coeffBytes)
    (x : Fin n → ZMod q) : decodeTPoly hwidth (encodeTPoly hwidth x) = x := by
  unfold decodeTPoly encodeTPoly
  rw [cast_cast]
  exact decodeP_encodeP hq x

/-- The concrete cyclic-convolution `CallSpec` over the `.TPolyMod q n` carrier,
    wired to the round-trip-verified `encodeTPoly`/`decodeTPoly`. -/
def cyclicConvCallSpecP {q n : ℕ} [NeZero q] [NeZero n]
    (hwidth : (TowerType.TPolyMod q n).storageBytes = n * coeffBytes)
    (leaf : String) : CallSpec :=
  fun fname _dt _argTs oldDest args =>
    if fname = leaf then
      let pick : (Σ t : TowerType, RustVal t) → (Fin n → ZMod q) := fun a =>
        if ht : a.1 = TowerType.TPolyMod q n then decodeTPoly hwidth (ht ▸ a.2) else 0
      match args with
      | a :: b :: _ =>
          if hd : _dt = TowerType.TPolyMod q n then
            hd ▸ encodeTPoly hwidth (cyclicConv n (pick a) (pick b))
          else oldDest
      | _ => oldDest
    else oldDest

/-- The concrete realizer `LeafSpec`. -/
def cyclicConvLeafSpecP {q n : ℕ} [NeZero q] [NeZero n]
    (hwidth : (TowerType.TPolyMod q n).storageBytes = n * coeffBytes)
    (leaf : String) (limbStore : LimbStoreSpec) : LeafSpec :=
  { call := cyclicConvCallSpecP hwidth leaf, limbStore := limbStore }

/-- **Unconditional kernel realization (no KAT, no abstract section).**  The
    concrete realizer `cyclicConvLeafSpecP` decodes its leaf-call value to the
    cyclic convolution for **every** input — proved by the round-trip
    `decodeTPoly_encodeTPoly` (valid for `q < 2^16`), not assumed via a test
    vector. -/
theorem nttKernelRealizesP_concrete {q n : ℕ} [NeZero q] [NeZero n]
    (hq : q < 65536)
    (hwidth : (TowerType.TPolyMod q n).storageBytes = n * coeffBytes)
    (leaf : String) (limbStore : LimbStoreSpec) :
    NttKernelRealizesP q n (decodeTPoly hwidth) leaf
      (cyclicConvLeafSpecP hwidth leaf limbStore) := by
  intro aVal bVal oldDest
  show decodeTPoly hwidth (cyclicConvCallSpecP hwidth leaf leaf (.TPolyMod q n)
      [.TPolyMod q n, .TPolyMod q n] oldDest
      [⟨.TPolyMod q n, aVal⟩, ⟨.TPolyMod q n, bVal⟩])
    = cyclicConv n (decodeTPoly hwidth aVal) (decodeTPoly hwidth bVal)
  simp only [cyclicConvCallSpecP, ite_true, dite_true]
  rw [decodeTPoly_encodeTPoly hq]

/-! ## §4  The unconditional ML-KEM realization (the deliverable)

Instantiating §3 at the ML-KEM parameters (`q = 3329`, `n = 256`, `ω = 17`) and
discharging the commuting square with the **proven** `isPrimitiveRoot_17_256` and
`n_ne_zero_3329` gives the full NTT-multiply realization with **no** KAT and **no**
abstract section hypothesis — the realization is proved for all inputs of the
concrete, spec-computing realizer with its round-trip-verified encoding. -/

/-- **ML-KEM NTT-multiply realization — UNCONDITIONAL.**  For the concrete
    realizer `cyclicConvLeafSpecP 3329 256 …` and the concrete, round-trip-verified
    `decodeP`/`encodeP` encoding, the full NTT-multiply realization
    `NttEmitRealizesP 3329 256 17 …` holds for every input.  No KAT hypothesis and
    no abstract `decode ∘ encode = id` assumption remain: the byte-level
    decode-equals-convolution fact is the theorem `decodeP_encodeP`, and the
    transform·pointwise·inverse = cyclic-convolution fact is the proven
    `isPrimitiveRoot_17_256` + `n_ne_zero_3329` via the commuting square.

    What is **not** proved here: that the jasmin-emitted machine bytes of the real
    `ntt_poly_mul_3329_256` kernel equal `cyclicConvLeafSpecP` (the owned-machine
    -code route — a separate follow-up). -/
theorem mlkem_nttEmitRealizes_concrete (limbStore : LimbStoreSpec) :
    NttEmitRealizesP 3329 256 (17 : ZMod 3329)
      (decodeTPoly (q := 3329) (n := 256) (by rfl))
      "ntt_poly_mul_3329_256"
      (cyclicConvLeafSpecP (q := 3329) (n := 256) (by rfl)
        "ntt_poly_mul_3329_256" limbStore) :=
  nttEmitRealizesP_of_cyclicConv (decodeTPoly (q := 3329) (n := 256) (by rfl))
    "ntt_poly_mul_3329_256" _
    isPrimitiveRoot_17_256 n_ne_zero_3329
    (nttKernelRealizesP_concrete (by decide) (by rfl)
      "ntt_poly_mul_3329_256" limbStore)

end CatCrypt.Crypto.SecureCompilation.ConcreteNttRealizer
