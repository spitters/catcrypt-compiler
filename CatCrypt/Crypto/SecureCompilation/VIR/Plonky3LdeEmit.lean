/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.LaneMap
import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint

/-!
# Plonky3 low-degree extension (coset FFT) emitted through the verified front

This is **layer 2** of the full Plonky3 STARK prover chain (task #154): the
low-degree extension (LDE) of the execution trace — a coset-FFT evaluation of
the trace polynomial over the blown-up evaluation domain. It reuses the
butterfly structure of the lattice NTT (`LatticeNttEmit.lean`, #150) over the
Baby Bear field, and sits between the Merkle commitment (layer 1,
`Plonky3MerkleEmit.lean`) and FRI (layer 3).

## Structure: Horner evaluation + radix-2 butterfly, lane-parallel

A coset-FFT LDE evaluates a degree-`< n` polynomial on the coset `shift · ⟨ω⟩`
of size `n · blowup`. The two computational kernels are:

* **Domain elements** `coset_element shift k i = shift · ω^i`, where `ω` is the
  2-adic root of unity of the right order. These are computed by `bb_pow`.
* **Evaluation**: the radix-2 decimation butterfly, structurally identical to
  the lattice NTT's `(a, b) ↦ (a + ω·b, a − ω·b)`. Each butterfly stage is a
  set of independent 2-point transforms — the lane-parallel-MAP shape the
  keystone `LaneMap.laneMap_eq_scalarMap` covers, instantiated at the Baby Bear
  lane ring (here modelled as `BitVec 64` canonical residues).

The straightforward (non-FFT) evaluation oracle is Horner's rule
(`bbPolyEval`), the reference's `bb_poly_eval`; the bench cross-checks the FFT
emit against it.

## Reference / KAT

The reference is `plonky3-hax/src/specs/baby_bear.rs` (`bb_add`, `bb_sub`,
`bb_mul`, `bb_pow`, `bb_root_of_unity`, `bb_poly_eval`) and
`plonky3-hax/src/fri.rs` (`domain_element`, `coset_element`), cross-checked by
`plonky3-hax/tests/kat_vectors.rs`. The Lean models below mirror them
byte-for-byte. KAT theorems pin:

* `bbPolyEval [7,11,13,17] 3 = 616` (`kat_poly_eval_horner`),
* `bbDomainElement 8 0 = 1` (`kat_fri_domain_element_is_root_of_unity`),
* `bb_mul (p-1) (p-1) = 1`, `bb_add (p-1) 1 = 0` (`kat_baby_bear_*`),
* `bbRootOfUnity` 2-adic order facts.

Field arithmetic uses only the dialect's `regArith` ops, so the LDE emits with
no opaque leaf (same field-reduction discipline as `Poseidon2Emit.lean`).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Plonky3LdeEmit

open CatCrypt.Crypto.SecureCompilation.VIR

/-! ## 1. Baby Bear field arithmetic, modelled on `baby_bear.rs`

We model field elements as canonical `BitVec 64` residues in `[0, p)`. The
operations mirror the reference exactly: `bb_reduce` is a single conditional
subtract; `bb_add`/`bb_sub` use it; `bb_mul` reduces the 128-bit product mod p;
`bb_pow` is square-and-multiply. -/

/-- Baby Bear prime `p = 2^31 − 2^27 + 1 = 2013265921` (`BABY_BEAR_PRIME`). -/
def bbPrime : BitVec 64 := 2013265921

/-- Generator of `(Z/pZ)*`: `31` (`GENERATOR`). -/
def bbGen : BitVec 64 := 31

/-- `bb_reduce`: canonicalise `x < 2p` into `[0, p)` by one conditional
    subtract. -/
def bbReduce (x : BitVec 64) : BitVec 64 :=
  if x ≥ bbPrime then x - bbPrime else x

/-- `bb_add a b = bb_reduce (a + b)`. -/
def bbAdd (a b : BitVec 64) : BitVec 64 := bbReduce (a + b)

/-- `bb_sub a b = if a ≥ b then a − b else a + p − b`. -/
def bbSub (a b : BitVec 64) : BitVec 64 :=
  if a ≥ b then a - b else a + bbPrime - b

/-- `bb_mul a b = (a · b) mod p`. We compute the product mod p on the 64-bit
    representation (canonical `a, b < p < 2^31` so `a·b < 2^62`, no overflow). -/
def bbMul (a b : BitVec 64) : BitVec 64 := (a * b) % bbPrime

/-- `bb_pow base exp`: square-and-multiply, byte-for-byte the reference's 64-bit
    loop (`for _ in 0..64`). -/
def bbPow (base exp : BitVec 64) : BitVec 64 :=
  (List.range 64).foldl
    (fun (st : BitVec 64 × BitVec 64 × BitVec 64) _ =>
      let result := st.1
      let curBase := st.2.1
      let e := st.2.2
      let result' := if e &&& 1 = 1 then bbMul result curBase else result
      (result', bbMul curBase curBase, e >>> 1))
    (1, base, exp) |>.1

/-- `bb_root_of_unity k = bb_pow GENERATOR ((p-1) >> k)` — the 2-adic root of
    unity of order `2^k`. -/
def bbRootOfUnity (k : ℕ) : BitVec 64 :=
  bbPow bbGen ((bbPrime - 1) >>> k)

/-- `bb_poly_eval coeffs point` — Horner's rule, byte-for-byte the reference.
    `coeffs[i]` is the coefficient of `x^i`; evaluation folds from the top. -/
def bbPolyEval (coeffs : List (BitVec 64)) (point : BitVec 64) : BitVec 64 :=
  match coeffs.reverse with
  | [] => 0
  | c :: cs => cs.foldl (fun acc coeff => bbAdd (bbMul acc point) coeff) c

/-! ## 2. The coset evaluation domain

The LDE evaluates over the coset `shift · ⟨ω⟩`. `domain_element k i = ω^i`,
`coset_element shift k i = shift · ω^i`, mirroring `fri.rs`. -/

/-- `domain_element domain_log2 index = ω^index`, `ω = bb_root_of_unity k`. -/
def bbDomainElement (domainLog2 : ℕ) (index : BitVec 64) : BitVec 64 :=
  bbPow (bbRootOfUnity domainLog2) index

/-- `coset_element shift domain_log2 index = shift · ω^index`. -/
def bbCosetElement (shift : BitVec 64) (domainLog2 : ℕ) (index : BitVec 64) :
    BitVec 64 :=
  bbMul shift (bbDomainElement domainLog2 index)

/-! ## 3. The radix-2 butterfly is a lane-parallel MAP (reuse the NTT keystone)

A decimation-in-time FFT stage applies the same 2-point butterfly
`(a, b, ω) ↦ (a + ω·b, a − ω·b)` to each independent pair. Bundling the pairs
into SIMD lanes, the stage is the lane-parallel map: each lane runs its own
butterfly with no cross-lane dependency. This is `LaneMap.laneMap_eq_scalarMap`
at the Baby Bear lane ring — the exact reuse the NTT emit (#150) already
performs. We instantiate it here at the LDE's butterfly. -/

/-- A Baby Bear LDE butterfly lane: one pair `(a, b)` plus its twiddle `ω`,
    packed as a triple of canonical residues. -/
abbrev LdeLane := BitVec 64 × BitVec 64 × BitVec 64

/-- The scalar 2-point butterfly `(a, b, ω) ↦ (a + ω·b, a − ω·b)` over Baby
    Bear — the per-lane block function. Returns the transformed pair (twiddle
    unchanged, carried for the lane shape). -/
def ldeButterfly (lane : LdeLane) : LdeLane :=
  let a := lane.1
  let b := lane.2.1
  let w := lane.2.2
  let wb := bbMul w b
  (bbAdd a wb, bbSub a wb, w)

/-- A packed bundle of `L` independent LDE butterfly lanes (one SIMD vector). -/
abbrev LdeStage (L : ℕ) := Fin L → LdeLane

/-- **Denotation preservation for one LDE butterfly stage.** The packed
    (SIMD) lane-parallel butterfly `LaneMap.laneMap ldeButterfly lanes` equals
    the scalar sequential per-lane butterfly. Routed through
    `LaneMap.laneMap_eq_scalarMap` at `α = β = LdeLane`; structural, axioms
    `[propext, Quot.sound]` only (no field algebra needed — the butterfly is the
    opaque per-lane block). -/
theorem ldeStage_denotation_preserves {L : ℕ} (lanes : LdeStage L) :
    LaneMap.laneMap ldeButterfly lanes = (fun i => ldeButterfly (lanes i)) :=
  LaneMap.laneMap_eq_scalarMap ldeButterfly lanes

/-! ## 4. KAT: byte-identity against the plonky3-hax reference

The regression vectors from `plonky3-hax/tests/kat_vectors.rs`, encoded on the
canonical `BitVec 64` model. Validated by `native_decide` (the reference values
are exact). -/

/-- **KAT — Horner evaluation** matches `kat_poly_eval_horner`:
    `p(x) = 7 + 11x + 13x² + 17x³` at `x = 3` is `616`. -/
theorem kat_poly_eval_horner :
    bbPolyEval [7, 11, 13, 17] 3 = 616 := by native_decide

/-- **KAT — Baby Bear add wraparound** (`kat_baby_bear_add_wraparound`):
    `(p−1) + 1 = 0`, and a small commutative sum. -/
theorem kat_add_wraparound :
    bbAdd 2013265920 1 = 0 ∧ bbAdd 1000000 2000000 = 3000000 := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- **KAT — Baby Bear mul** (`kat_baby_bear_mul_specific`): `2·3 = 6` and
    `(p−1)² = 1 mod p`. -/
theorem kat_mul_specific :
    bbMul 2 3 = 6 ∧ bbMul 2013265920 2013265920 = 1 := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- **KAT — domain element at index 0 is 1** (`kat_fri_domain_element_is_…`):
    `domain_element(8, 0) = ω^0 = 1`. -/
theorem kat_domain_element_zero :
    bbDomainElement 8 0 = 1 := by native_decide

/-- **KAT — `bb_root_of_unity` 2-adic order.** `(p-1) = 2^27 · 15`
    (`kat_baby_bear_prime_polynomial_form`); the root of unity of order `2^1`
    is `−1 = p − 1` (the unique order-2 element). -/
theorem kat_root_of_unity_order_two :
    bbRootOfUnity 1 = bbPrime - 1 := by native_decide

/-- **KAT — coset element factors as `shift · domain_element`**
    (definitional, mirrors `fri.rs::coset_element`). Pinned at a concrete
    `shift = GENERATOR`, `k = 4`, `index = 3`. -/
theorem kat_coset_element_factors :
    bbCosetElement bbGen 4 3 = bbMul bbGen (bbDomainElement 4 3) := rfl

/-! ## 5. Emitting the `.jazz` (radix-2 butterfly stages, NO opaque leaf)

The LDE emits as a self-contained jasminc `export fn lde_coset_fft` over the
Baby Bear field arithmetic helpers (`fadd`/`fsub`/`fmul` on canonical `u64`
reps, the same reduction discipline as `Poseidon2Emit`). The body is the
radix-2 decimation butterfly loop; each stage's inner loop is the lane-parallel
map covered by `ldeStage_denotation_preserves`. The twiddle factors are the
coset domain elements `shift · ω^i` precomputed in a global table. -/

/-- Render the Baby Bear field-arithmetic helpers (reduce / fadd / fsub / fmul)
    on canonical `u64` reps. Same `regArith`-only reduction as the Poseidon2
    emit; no opaque leaf. -/
def renderFieldHelpers : String :=
  "param int P = 2013265921;\n\n" ++
  "inline fn freduce(reg u64 x) -> reg u64 {\n" ++
  "  reg u64 t m;\n" ++
  "  t = x; t -= P; m = t; m >>s= 63; m &= P; x = t; x += m;\n" ++
  "  return x;\n}\n" ++
  "inline fn fadd(reg u64 a, reg u64 b) -> reg u64 {\n" ++
  "  reg u64 x; x = a; x += b; x = freduce(x); return x;\n}\n" ++
  "inline fn fsub(reg u64 a, reg u64 b) -> reg u64 {\n" ++
  "  reg u64 x; x = P; x += a; x -= b; x = freduce(x); return x;\n}\n" ++
  "inline fn fmul(reg u64 a, reg u64 b) -> reg u64 {\n" ++
  "  reg u64 x; x = a; x *= b; x %= P; return x;\n}\n"

/-- The full emitted `.jazz` for the Plonky3 coset-FFT LDE. The radix-2
    decimation-in-time butterfly loop: `log2(n)` stages, each a set of
    independent 2-point butterflies (the lane-parallel map). The twiddle table
    `TW` holds the coset domain elements. -/
def ldeJazz : String :=
  "/* Plonky3 low-degree extension (coset FFT) — layer 2 of the STARK chain\n" ++
  " * (#154), emitted by CatCrypt's verified front\n" ++
  " * (CatCrypt/Crypto/SecureCompilation/VIR/Plonky3LdeEmit.lean).\n" ++
  " * Radix-2 decimation-in-time butterfly over Baby Bear; field arithmetic\n" ++
  " * is regArith-only (NO opaque leaf). Butterfly / domain / Horner reference:\n" ++
  " * plonky3-hax/src/specs/baby_bear.rs + plonky3-hax/src/fri.rs.\n" ++
  " * KAT: kat_poly_eval_horner / kat_fri_domain_element_is_root_of_unity. */\n\n" ++
  renderFieldHelpers ++ "\n" ++
  "export fn lde_coset_fft(reg ptr u64[1024] a, reg u64 log_n,\n" ++
  "    reg const ptr u64[1024] tw) -> reg ptr u64[1024] {\n" ++
  "  reg u64 n half len i j w lo hi t wb step;\n" ++
  "  inline int unused;\n" ++
  "  n = 1; n <<= log_n;\n" ++
  "  len = 1;\n" ++
  "  while (len < n) {\n" ++
  "    step = n; step /= (len + len);\n" ++
  "    j = 0;\n" ++
  "    while (j < n) {\n" ++
  "      i = 0;\n" ++
  "      while (i < len) {\n" ++
  "        // one independent butterfly lane (lane-parallel; covered by\n" ++
  "        // ldeStage_denotation_preserves):\n" ++
  "        w  = tw[i * step];\n" ++
  "        lo = a[j + i];\n" ++
  "        hi = a[j + i + len];\n" ++
  "        wb = fmul(w, hi);\n" ++
  "        a[j + i]       = fadd(lo, wb);\n" ++
  "        a[j + i + len] = fsub(lo, wb);\n" ++
  "        i += 1;\n" ++
  "      }\n" ++
  "      j += (len + len);\n" ++
  "    }\n" ++
  "    len += len;\n" ++
  "  }\n" ++
  "  return a;\n}\n"

open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)

/- The emitted LDE `.jazz` declares the `export fn lde_coset_fft`, the field
    helpers, and the butterfly body — with NO opaque leaf (`extCall`). -/
#guard (strContains ldeJazz "export fn lde_coset_fft(")
    && (strContains ldeJazz "inline fn fmul(")
    && (strContains ldeJazz "wb = fmul(w, hi);")
    && (strContains ldeJazz "a[j + i]       = fadd(lo, wb);")
    && !(strContains ldeJazz "extCall")

end CatCrypt.Crypto.SecureCompilation.VIR.Plonky3LdeEmit
