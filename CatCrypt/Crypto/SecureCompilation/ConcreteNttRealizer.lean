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
# A concrete cyclic-convolution leaf realizer over `.TPolyMod q n`

The generic NTT-multiply emit→value seam (`GenericNttEmitValue`) discharges the
realization down to a leaf-realization predicate that its instantiation at
`q = 3329`, `n = 256` takes as a hypothesis (`mlkem_nttEmitRealizes_of_kernel`
assumes `NttKernelRealizes … leafSpec`: the leaf-call value decodes to the
cyclic convolution).  Its non-vacuity witnesses (`nttKernelRealizes_canonical`,
`mlkem_nttKernelRealizes_canonical`) exhibit a `LeafSpec` satisfying the
predicate parametrically over an abstract `encode`/`decode` pair with a section
hypothesis (`hsection : ∀ p, decode (encode p) = p`).

This module supplies a concrete, proved section, so the realization holds for a
spec-computing realizer with no hypothesis.  It provides:

* the `RustVal (.TPolyMod q n)` carrier (a byte array
  `Fin storageBytes → BitVec 8`) with a two-bytes-per-coefficient little-endian
  `encodeP`/`decodeP` pair, and
* the round-trip theorem `decodeP_encodeP : ∀ x, decodeP (encodeP x) = x`,
  valid for every coefficient vector whenever `q < 2^16`.

From that round-trip the leaf realizer `cyclicConvLeafSpecP` computes the cyclic
convolution (`NttKernelRealizesP`), and composing with the primitive-root facts
`isPrimitiveRoot_17_256`, `n_ne_zero_3329` through the commuting-square
discharge gives `mlkem_nttEmitRealizes_concrete`: the realization of
`nttMul 256 17` over `ZMod 3329`.

## What `nttMul 256 17` is

`nttMul 256 17` over `ZMod 3329` equals `cyclicConv 256`, multiplication in
`Z_3329[X]/(X^256 − 1)`.  It is not FIPS 203's ML-KEM transform: ML-KEM's NTT is
the incomplete 7-layer transform of `Z_3329[X]/(X^256 + 1)` into 128 quadratic
residues, and no full negacyclic diagonalisation exists at this modulus because
`3328 = 2^8 · 13` gives `ZMod 3329` no element of order 512
(`ConcreteNttInstances.lean`, "ML-KEM is cyclic here, not negacyclic").  The
jasmin leaf named `ntt_poly_mul_3329_256` in
`bench/mlkem_compare/include/leaves.jinc` is formosa-mlkem's `_poly_basemul`,
an NTT-domain pointwise multiply on already-transformed data, which is a third
function; the string is used here only as the `LeafSpec` key.  The owned ML-KEM
NTT that passes the NIST KAT is a separate artifact and is not described by this
module.

## The `.TPolyMod` carrier vs the generic `.TFp` predicate

`GenericNttEmitValue`'s `NttKernelRealizes`/`NttEmitRealizes` fix the carrier to
`RustVal .TFp = JArray 48 = Fin 48 → BitVec 8`, 48 bytes = 384 bits.  No
round-trip `decode ∘ encode = id` exists on that carrier for `Fin 256 → ZMod 3329`:
an injection needs `≥ log₂(3329²⁵⁶) ≈ 3072` bits (pigeonhole).  The carrier
`RustVal (.TPolyMod 3329 256)` has `256 · 2 = 512` bytes = 4096 bits, which
suffices, and it is the TowerType the compiler uses for degree-256 polynomials
mod 3329.  The realization predicates are therefore re-stated over
`.TPolyMod q n` and the same commuting-square discharge is re-run; the
convolution content `nttMul_eq_cyclicConv'` is reused unchanged.

## Scope

* Proved: there is a concrete leaf realizer (`cyclicConvLeafSpecP`) and a
  concrete, round-trip-verified byte encoding (`encodeP`/`decodeP`,
  `decodeP_encodeP`) under which `NttEmitRealizesP` holds for all inputs.  The
  byte-level decode-equals-convolution fact is a theorem, not a test vector.
* Not proved: any relation between this realizer and emitted machine bytes.  No
  theorem here relates `cyclicConvLeafSpecP` to the bytes of any kernel.

## References
* NIST FIPS 203 (ML-KEM), FIPS 204 (ML-DSA).  The FIPS 203 transform is the
  incomplete 7-layer NTT of `X^256 + 1`, which differs from the cyclic
  convolution realized here as described above.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ConcreteNttRealizer

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.GenericNttEmitValue
open CatCrypt.Crypto.Optimizer.Lattice.NTTMultiplyCorrectGeneric
open CatCrypt.Crypto.Lattice.CyclicConvolutionGeneric
open CatCrypt.Crypto.Lattice.ConcreteNttRoots

/-! ## §1  Concrete, round-trip-verified byte encoding over `.TPolyMod q n`

`RustVal (.TPolyMod q n) = JArray (.TPolyMod q n).storageBytes`, a byte
array.  For `q < 2^16` each coefficient fits in two bytes; we lay them out
little-endian, two bytes per coefficient.  The decode reads the two bytes back as
a `ZMod q`.  The round-trip is a per-coefficient `Nat`-arithmetic fact. -/

/-- Byte width per coefficient used by our concrete layout: two bytes
    (little-endian), sufficient whenever `q < 2^16`. -/
def coeffBytes : ℕ := 2

/-- The concrete carrier for a length-`n` coefficient vector mod `q`:
    `n` coefficients laid out two bytes each, little-endian, as a
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

/-- The round-trip of the byte codec: for any modulus `q < 2^16`, decoding the
    little-endian byte encoding of a coefficient vector returns the vector, for
    all inputs. -/
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

The generic predicates in `GenericNttEmitValue` fix the `.TFp` carrier (48
bytes), which is too small for a round-trip (see the module docstring).  The
same two predicates are re-stated over `RustVal (.TPolyMod q n)`, the carrier
the compiler uses for degree-`n` polynomials mod `q` (512 bytes at
`q = 3329`, `n = 256`), and the identical commuting-square discharge is re-run.
Only the carrier TowerType differs; the convolution content
(`nttMul_eq_cyclicConv'`) is reused unchanged.

The carrier `RustVal (.TPolyMod q n) = JArray ((.TPolyMod q n).storageBytes)`
equals `PolyBytes n = JArray (n · coeffBytes)` definitionally exactly when
`(.TPolyMod q n).storageBytes = n · coeffBytes`, i.e. when `q` needs two bytes
per coefficient.  That fact is a hypothesis `hwidth` cast through, so the
predicates and the discharge stay parametric in `q, n` (the literals `3329`,
`256` satisfy `hwidth` by `rfl`, and `ZMod 3329` is a field, discharging the
`Field` instance `nttMul_eq_cyclicConv'` needs). -/

/-- The `.TPolyMod`-carrier cyclic-convolution kernel-realization predicate: the
    leaf-call value decodes to the length-`n` cyclic convolution.  Identical in
    shape to `GenericNttEmitValue.NttKernelRealizes`, but over the full-width
    `.TPolyMod q n` byte carrier. -/
def NttKernelRealizesP (q n : ℕ) [NeZero q] [NeZero n]
    (decode : RustVal (.TPolyMod q n) → (Fin n → ZMod q))
    (leaf : String) (leafSpec : LeafSpec) : Prop :=
  ∀ (aVal bVal oldDest : RustVal (.TPolyMod q n)),
    decode
        (leafSpec.call leaf (.TPolyMod q n) [.TPolyMod q n, .TPolyMod q n] oldDest
          [⟨.TPolyMod q n, aVal⟩, ⟨.TPolyMod q n, bVal⟩])
      = cyclicConv n (decode aVal) (decode bVal)

/-- The `.TPolyMod`-carrier `nttMul` realization predicate: the leaf-call value
    decodes to `nttMul n ω …` (transform, pointwise product, inverse
    transform at the root `ω`). -/
def NttEmitRealizesP (q n : ℕ) [NeZero q] [NeZero n] [Fact (Nat.Prime q)] (ω : ZMod q)
    (decode : RustVal (.TPolyMod q n) → (Fin n → ZMod q))
    (leaf : String) (leafSpec : LeafSpec) : Prop :=
  ∀ (aVal bVal oldDest : RustVal (.TPolyMod q n)),
    decode
        (leafSpec.call leaf (.TPolyMod q n) [.TPolyMod q n, .TPolyMod q n] oldDest
          [⟨.TPolyMod q n, aVal⟩, ⟨.TPolyMod q n, bVal⟩])
      = nttMul n ω (decode aVal) (decode bVal)

/-- Commuting-square discharge over `.TPolyMod`, identical to
    `nttEmitRealizes_of_cyclicConv` on the `.TPolyMod` carrier: a primitive
    `n`-th root `ω` with `(n : ZMod q) ≠ 0` rewrites `nttMul = cyclicConv`
    (`nttMul_eq_cyclicConv'`), lifting the kernel realization to the `nttMul`
    realization. -/
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

`cyclicConvLeafSpecP` is the canonical realizer wired to the concrete
`encodeP`/`decodeP` of §1: at the named leaf it decodes both polynomial
arguments, computes their cyclic convolution, and re-encodes; off-leaf it
returns `oldDest`.  Because the round-trip `decodeP_encodeP` is a theorem,
`NttKernelRealizesP` holds with no `hsection` hypothesis.

`hwidth : (.TPolyMod q n).storageBytes = n * coeffBytes` makes `RustVal
(.TPolyMod q n)` equal to `PolyBytes n`, letting the byte-level `encodeP`/`decodeP`
serve as the carrier codec.  At `q = 3329`, `n = 256` it holds by `rfl`. -/

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
  erw [cast_cast]
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

/-- The concrete realizer `cyclicConvLeafSpecP` decodes its leaf-call value to
    the cyclic convolution for every input, by the round-trip
    `decodeTPoly_encodeTPoly` (valid for `q < 2^16`).  No KAT and no abstract
    section hypothesis. -/
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

/-! ## §4  The realization at `q = 3329`, `n = 256`, `ω = 17`

Instantiating §3 at `q = 3329`, `n = 256`, `ω = 17` and discharging the
commuting square with `isPrimitiveRoot_17_256` and `n_ne_zero_3329` gives the
`nttMul 256 17` realization with no KAT and no abstract section hypothesis, for
all inputs of the concrete, spec-computing realizer with its round-trip-verified
encoding.  `nttMul 256 17` over `ZMod 3329` is the cyclic convolution of
`X^256 − 1`, not FIPS 203's transform of `X^256 + 1` (module docstring). -/

/-- For the concrete realizer `cyclicConvLeafSpecP 3329 256 …` and the
    round-trip-verified `decodeP`/`encodeP` encoding, the realization
    `NttEmitRealizesP 3329 256 17 …` holds for every input.  No KAT hypothesis
    and no abstract `decode ∘ encode = id` assumption: the byte-level
    decode-equals-convolution fact is the theorem `decodeP_encodeP`, and the
    transform·pointwise·inverse = cyclic-convolution fact is
    `isPrimitiveRoot_17_256` + `n_ne_zero_3329` via the commuting square.

    The object realized is `nttMul 256 17 = cyclicConv 256` over `ZMod 3329`,
    multiplication in `Z_3329[X]/(X^256 − 1)`; it is not FIPS 203's ML-KEM
    transform.  The leaf name `"ntt_poly_mul_3329_256"` is the `LeafSpec` key
    and not a reference to the jasmin function of that name.  No statement about
    emitted machine bytes is made here. -/
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
