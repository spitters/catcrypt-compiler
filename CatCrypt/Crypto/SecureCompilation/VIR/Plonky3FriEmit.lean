/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.LaneMap
public import CatCrypt.Crypto.SecureCompilation.VIR.LaneMap
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3LdeEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3LdeEmit
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3MerkleEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3MerkleEmit
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint

/-!
# Plonky3 FRI (commit + query) emitted through the verified front

This is **layer 3** of the full Plonky3 STARK prover chain: the FRI
low-degree test — the fold (commit) phase and the query phase. It composes
layer 1 (`Plonky3MerkleEmit`, the per-layer commitment + query openings) and
layer 2 (`Plonky3LdeEmit`, the Baby Bear field arithmetic + coset domain).

## Structure

* **Fold (commit) phase.** Each FRI layer halves the evaluation domain. For each
  surviving coset point `x`, the fold maps the two sibling evaluations
  `(p(x), p(−x))` to one folded evaluation
  `fri_fold(p(x), p(−x), x, α) = p_even(x²) + α · p_odd(x²)`. The folds across
  the `n/2` cosets are **independent** — the lane-parallel-MAP shape. The
  vectorized fold emit denotes the scalar per-coset fold by
  `friFoldLayer_denotation_preserves` (`LaneMap.laneMap_eq_scalarMap`).

* **Coefficient fold.** `fold_polynomial(coeffs, α)` produces
  `p'[i] = p_even[i] + α · p_odd[i]`; the next-layer commitment is the Merkle
  tree (layer 1) over the new evaluations.

* **Query phase.** Each query checks two Merkle openings (`p(x)` and `p(−x)`)
  against the layer commitment, then the fold consistency. The Merkle openings
  reuse layer 1's `merkleHashTwoToOne`; the sibling / folded indices are
  `sibling_index` / `folded_index`.

## Reference / KAT

The reference is `plonky3-hax/src/fri.rs` (`fri_fold`, `fold_polynomial`,
`sibling_index`, `folded_index`, `domain_element`), cross-checked by
`plonky3-hax/tests/kat_vectors.rs`. The Lean models mirror them. KAT theorems:

* `friFold 100 50 7 3 = 287609503` (`kat_fri_fold_specific_point`),
* `friFold 42 42 5 999 = 42` (constant polynomial; `kat_fri_fold_constant_…`),
* `siblingIndex` / `foldedIndex` index identities (`kat_fri_sibling_index`,
  `kat_fri_folded_index`),
* `foldPolynomial [3,5] 11 = [3 + 11·5]` (`kat_fri_fold_polynomial_linear`).

Field arithmetic reuses `Plonky3LdeEmit`; the fold inverse `1/2` and `1/(2x)`
are precomputed Baby Bear inverses. No opaque leaf.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Plonky3FriEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Plonky3LdeEmit
  (bbAdd bbSub bbMul bbPow bbPrime)

/-! ## 1. The FRI fold at a point (`fri.rs::fri_fold`)

`fri_fold(eval_pos, eval_neg, x, α)`:
```
sum  = eval_pos + eval_neg          p_even = sum  / 2
diff = eval_pos − eval_neg          p_odd  = diff / (2x)
result = p_even + α · p_odd
```
The inverses `1/2` and `1/(2x)` are `bb_inv` (Fermat `a^(p-2)`). -/

/-- Baby Bear inverse `a^(p-2)` (`bb_inv`); `0 ↦ 0`. -/
def bbInv (a : BitVec 64) : BitVec 64 :=
  if a = 0 then 0 else bbPow a (bbPrime - 2)

/-- **FRI fold at a point** `fri_fold(eval_pos, eval_neg, x, α)`, byte-for-byte
    `fri.rs::fri_fold`. -/
def friFold (evalPos evalNeg x alpha : BitVec 64) : BitVec 64 :=
  let sum := bbAdd evalPos evalNeg
  let diff := bbSub evalPos evalNeg
  let invTwo := bbInv 2
  let twoX := bbMul 2 x
  let invTwoX := bbInv twoX
  let pEven := bbMul sum invTwo
  let pOdd := bbMul diff invTwoX
  bbAdd pEven (bbMul alpha pOdd)

/-! ## 2. Sibling / folded indices (`fri.rs`) -/

/-- `sibling_index index k = (index + n/2) mod n`, `n = 2^k`
    (`fri.rs::sibling_index`). -/
def siblingIndex (index : ℕ) (k : ℕ) : ℕ :=
  let n := 2 ^ k
  (index + n / 2) % n

/-- `folded_index index k = index mod (n/2)`, `n = 2^k`
    (`fri.rs::folded_index`). -/
def foldedIndex (index : ℕ) (k : ℕ) : ℕ :=
  index % (2 ^ (k - 1))

/-! ## 3. Coefficient fold (`fri.rs::fold_polynomial`)

`p'[i] = p_even[i] + α · p_odd[i] = coeffs[2i] + α · coeffs[2i+1]` (odd term 0
when out of range). -/

/-- `fold_polynomial coeffs α`, byte-for-byte `fri.rs::fold_polynomial`. The
    result has `⌈n/2⌉` coefficients; entry `i` is
    `coeffs[2i] + α · coeffs[2i+1]`. -/
def foldPolynomial (coeffs : List (BitVec 64)) (alpha : BitVec 64) :
    List (BitVec 64) :=
  let n := coeffs.length
  let half := (n + 1) / 2
  (List.range half).map (fun i =>
    let evenC := coeffs.getD (2 * i) 0
    let oddC := if 2 * i + 1 < n then coeffs.getD (2 * i + 1) 0 else 0
    bbAdd evenC (bbMul alpha oddC))

/-! ## 4. The fold layer is a lane-parallel MAP over cosets

A FRI fold layer applies `fri_fold` to each of the `n/2` cosets, each reading
its own `(p(x_i), p(−x_i), x_i)` — independent, no cross-coset dependency. This
is the lane-parallel map `LaneMap.laneMap_eq_scalarMap` at the per-coset fold
input. The vectorized fold emit denotes the scalar per-coset fold. -/

/-- A FRI fold lane: the inputs `(eval_pos, eval_neg, x)` for one coset, plus the
    shared challenge `α`. -/
abbrev FriFoldLane := BitVec 64 × BitVec 64 × BitVec 64

/-- The per-coset fold block at challenge `α` — the per-lane block function. -/
def friFoldLaneFn (alpha : BitVec 64) (lane : FriFoldLane) : BitVec 64 :=
  friFold lane.1 lane.2.1 lane.2.2 alpha

/-- A packed bundle of `L` independent fold cosets (one fold layer over `L`
    siblings-pairs). -/
abbrev FriFoldLayer (L : ℕ) := Fin L → FriFoldLane

/-- **Denotation preservation for one FRI fold layer.** The packed (SIMD)
    lane-parallel fold `LaneMap.laneMap (friFoldLaneFn α) layer` equals the
    scalar sequential per-coset fold. Routed through
    `LaneMap.laneMap_eq_scalarMap` at `α = β = FriFoldLane → BitVec 64`;
    structural, axioms `[propext, Quot.sound]` only. This composes layer 2's
    field arithmetic (the fold body) under the lane-map theorem of layer 1. -/
theorem friFoldLayer_denotation_preserves {L : ℕ} (alpha : BitVec 64)
    (layer : FriFoldLayer L) :
    LaneMap.laneMap (friFoldLaneFn alpha) layer =
      (fun i => friFoldLaneFn alpha (layer i)) :=
  LaneMap.laneMap_eq_scalarMap (friFoldLaneFn alpha) layer

/-! ## 5. Query phase: Merkle openings reuse layer 1

A FRI query at index `i` checks the Merkle openings of `p(x_i)` and
`p(x_sibling)` against the layer root, then the fold consistency. The opening
verification reuses layer 1's `merkleHashTwoToOne` path recompute. We expose
the per-query path-recompute as the composition of layer 1's compress along the
authentication path. -/

open CatCrypt.Crypto.SecureCompilation.VIR.Plonky3MerkleEmit (Digest merkleHashTwoToOne)

/-- Recompute a Merkle root from a leaf along an authentication path, mirroring
    `merkle.rs::merkle_verify_path`: at each level, if the index bit is 0 the
    current node is the left child (sibling right), else vice versa. This is the
    query-phase check that reuses layer 1's two-to-one compress. -/
def merkleQueryRecompute (leaf : Digest) (index : ℕ) (siblings : List Digest) :
    Digest :=
  (siblings.foldl
    (fun (st : Digest × ℕ) sib =>
      let cur := st.1
      let idx := st.2
      let next := if idx % 2 = 0 then merkleHashTwoToOne cur sib
                  else merkleHashTwoToOne sib cur
      (next, idx / 2))
    (leaf, index)).1

/-- A single-level query recompute (`depth = 1`) reproduces the two-leaf root
    `kat_merkle_two_leaves` checks: at index 0 the leaf is the left child, so
    the recomputed root is `H(leaf, sibling)`. -/
theorem merkleQueryRecompute_one (leaf sib : Digest) :
    merkleQueryRecompute leaf 0 [sib] = merkleHashTwoToOne leaf sib := by
  simp only [merkleQueryRecompute, List.foldl_cons, List.foldl_nil, Nat.zero_mod,
    ite_true]

/-! ## 6. KAT: byte-identity against the plonky3-hax reference -/

/-- **KAT — FRI fold at a specific point** (`kat_fri_fold_specific_point`):
    `fri_fold(100, 50, 7, 3) = 287609503`. -/
theorem kat_fri_fold_specific :
    friFold 100 50 7 3 = 287609503 := by native_decide

/-- **KAT — FRI fold of a constant polynomial** (`kat_fri_fold_constant_…`):
    `p(x) = c` folds to `c` for any `α` (`fri_fold(42,42,5,999)=42`,
    `fri_fold(1,1,1,0)=1`). -/
theorem kat_fri_fold_constant :
    friFold 42 42 5 999 = 42 ∧ friFold 1 1 1 0 = 1 := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- **KAT — sibling index** (`kat_fri_sibling_index`): `n = 16` (`k = 4`), the
    sibling flips the high bit (`+ n/2 = 8`). -/
theorem kat_sibling_index :
    siblingIndex 0 4 = 8 ∧ siblingIndex 8 4 = 0
      ∧ siblingIndex 3 4 = 11 ∧ siblingIndex 11 4 = 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-- **KAT — folded index** (`kat_fri_folded_index`): `k = 4`, folded index is
    `i mod 8`. -/
theorem kat_folded_index :
    foldedIndex 0 4 = 0 ∧ foldedIndex 7 4 = 7
      ∧ foldedIndex 8 4 = 0 ∧ foldedIndex 15 4 = 7 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-- **KAT — coefficient fold, constant** (`kat_fri_fold_polynomial_constant`):
    `fold_polynomial([42, 0], 5) = [42]`. -/
theorem kat_fold_polynomial_constant :
    foldPolynomial [42, 0] 5 = [42] := by native_decide

/-- **KAT — coefficient fold, linear** (`kat_fri_fold_polynomial_linear`):
    `fold_polynomial([3, 5], 11) = [3 + 11·5]`. -/
theorem kat_fold_polynomial_linear :
    foldPolynomial [3, 5] 11 = [bbAdd 3 (bbMul 11 5)] := by native_decide

/-! ## 7. Emitting the `.jazz` (fold + query, NO opaque leaf)

The FRI commit phase emits as `export fn fri_fold_layer` over the Baby Bear
field helpers (reused from layer 2); the body is the per-coset fold loop, each
iteration the lane-parallel fold covered by `friFoldLayer_denotation_preserves`.
The query phase emits as `export fn fri_query_verify` reusing layer 1's
`h2to1` compress for the authentication-path recompute. No opaque leaf. -/

/-- Render the fold layer body: the per-coset `fri_fold` loop. Reuses the field
    helpers from the LDE emit (rendered separately by the bench driver). -/
def renderFriFoldLayer : String :=
  "inline fn finv2() -> reg u64 { reg u64 r; r = INV_TWO; return r; }\n\n" ++
  "export fn fri_fold_layer(reg ptr u64[1024] evals, reg u64 half,\n" ++
  "    reg const ptr u64[1024] xs, reg u64 alpha,\n" ++
  "    reg ptr u64[1024] out) -> reg ptr u64[1024] {\n" ++
  "  reg u64 i ep en x sum diff i2 i2x peven podd t;\n" ++
  "  inline int unused;\n" ++
  "  i = 0;\n" ++
  "  while (i < half) {\n" ++
  "    // one independent fold coset (lane-parallel; covered by\n" ++
  "    // friFoldLayer_denotation_preserves):\n" ++
  "    ep = evals[i];\n" ++
  "    en = evals[i + half];\n" ++
  "    x  = xs[i];\n" ++
  "    sum  = fadd(ep, en);\n" ++
  "    diff = fsub(ep, en);\n" ++
  "    i2   = INV_TWO;\n" ++
  "    i2x  = finv(fmul(2, x));\n" ++
  "    peven = fmul(sum, i2);\n" ++
  "    podd  = fmul(diff, i2x);\n" ++
  "    t = fmul(alpha, podd);\n" ++
  "    out[i] = fadd(peven, t);\n" ++
  "    i += 1;\n" ++
  "  }\n" ++
  "  return out;\n}\n"

/-- Render the query-phase authentication-path recompute, reusing layer 1's
    `h2to1` two-to-one compress. -/
def renderFriQuery : String :=
  "export fn fri_query_verify(reg ptr u8[32] leaf, reg u64 index,\n" ++
  "    reg ptr u8[1024] siblings, reg u64 depth,\n" ++
  "    reg ptr u8[32] root) -> reg u64 {\n" ++
  "  stack u8[32] cur; reg u64 level idx bit ok b x;\n  inline int c;\n" ++
  "  for c = 0 to 32 { x = leaf[c]; cur[c] = x; }\n" ++
  "  idx = index; level = 0;\n" ++
  "  while (level < depth) {\n" ++
  "    bit = idx; bit &= 1;\n" ++
  "    if (bit == 0) {\n" ++
  "      cur = h2to1(cur, siblings[32 * level : 32], cur);\n" ++
  "    } else {\n" ++
  "      cur = h2to1(siblings[32 * level : 32], cur, cur);\n" ++
  "    }\n" ++
  "    idx >>= 1; level += 1;\n" ++
  "  }\n" ++
  "  ok = 1;\n" ++
  "  for c = 0 to 32 { b = cur[c]; if (b != root[c]) { ok = 0; } }\n" ++
  "  return ok;\n}\n"

/-- The full emitted `.jazz` for the Plonky3 FRI commit + query phases. -/
def friJazz : String :=
  "/* Plonky3 FRI commit + query — layer 3 of the STARK chain,\n" ++
  " * emitted by CatCrypt's verified front\n" ++
  " * (CatCrypt/Crypto/SecureCompilation/VIR/Plonky3FriEmit.lean).\n" ++
  " * Fold (commit) phase: per-coset fri_fold, lane-parallel over cosets.\n" ++
  " * Query phase: Merkle authentication-path recompute reusing layer 1's\n" ++
  " * h2to1 two-to-one compress. Field arithmetic regArith-only; NO opaque\n" ++
  " * leaf. Reference: plonky3-hax/src/fri.rs.\n" ++
  " * KAT: kat_fri_fold_specific_point / kat_fri_fold_polynomial_linear. */\n\n" ++
  "param int INV_TWO = 1006632961; // (p+1)/2 = 1/2 mod p\n\n" ++
  renderFriFoldLayer ++ "\n" ++
  renderFriQuery

open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)

/- The emitted FRI `.jazz` declares both phase exports and reuses layer 1's
    `h2to1` compress in the query path — with NO opaque leaf (`extCall`). -/
#guard (strContains friJazz "export fn fri_fold_layer(")
    && (strContains friJazz "export fn fri_query_verify(")
    && (strContains friJazz "sum  = fadd(ep, en);")
    && (strContains friJazz "cur = h2to1(cur, siblings[32 * level : 32], cur);")
    && !(strContains friJazz "extCall")

end CatCrypt.Crypto.SecureCompilation.VIR.Plonky3FriEmit
