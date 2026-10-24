/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.MlkemNttPermutation

/-!
# Full multi-layer assembly: owned routed combine tree = abstract `dft` to depth `n`

`MlkemNttEndToEnd.lean` closed the per-layer routed combine tie at *every*
depth (`nttRec_succ_routed_is_combine`, `nttRec_routed_combine_descent`) and a
*two-layer* end-to-end fragment reaching `dft 4`
(`dft4_routed_two_layer_combine`).  Its precisely-named open item was the
**assembly of all layers** — iterating the single deinterleave permutation
*between every pair of adjacent layers* down the full recursion, not just at one
boundary.

This module supplies that assembly, by induction on depth.  The headline is a
**full-depth `n`-layer** statement (instantiated at `n = 8` to give the complete
owned `dft 256` routed tree).

## What this module ADDS

* **`routedNtt`** — a recursive evaluator that, at *every* layer, threads the
  deinterleave permutation: at depth `e+1` it deinterleaves its input into the
  blocked `[evens ‖ odds]` layout `v = (reindex e x) ∘ deinterleave (2^e)`,
  recurses (via `routedNtt e`) on the lower `[0,2^e)` and upper `[2^e,2·2^e)`
  halves of `v`, and butterfly-combines with the owned `combine2` atom.  This is
  the per-layer routed combine atom of `MlkemNttEndToEnd` *iterated to full
  depth* — the deinterleave permutation appears at each of the `e` layers.

* **`routedNtt_eq_nttRec`** — by induction on `e`, the routed tree computes
  exactly the abstract recursion: `routedNtt e ω x = nttRec e ω x`.  The
  inductive step is `nttRec_succ_routed_is_combine` (the per-layer routed tie),
  with the deinterleave routing threaded at *this* layer and the induction
  hypothesis supplying the routed half-transforms one layer down.

* **`routedNtt_eq_dft`** — composing with `nttRec_eq_dft`: the fully-routed
  owned combine tree computes the abstract `dft (2^e)`, for any depth `e` whose
  twiddle is a `2^e`-th root of unity.

* **`routedNtt256_eq_dft256`** — the headline at `n = 8`: the **8-layer** routed
  combine tree (deinterleave permutation threaded between all 8 layers) is the
  abstract ML-KEM-length transform `dft 256`.

This module is **fully abstract**: it states the routed combine tree as a
recursion over an arbitrary `CommRing` and proves it equal to the abstract `dft`.
The `combine2` butterfly atom (`a + ω·b`) is inlined; there is no
machine-realization (`runZBlock`/`ZState`/Montgomery-stage) import.  The
owned-machine Montgomery-form lane tie lives in the separate realization web and
is **not** required for the `dft 256` result here.

## Scope — what depth is closed, what remains

CLOSED here:

* the **full-depth** (`n`-layer, hence `8`-layer = `dft 256`) assembly of the
  routed combine tree with the deinterleave permutation threaded between *every*
  adjacent pair of layers (`routedNtt`, `routedNtt_eq_nttRec`,
  `routedNtt_eq_dft`, `routedNtt256_eq_dft256`).  Each layer's even/odd operand
  layout is produced by that layer's `deinterleave (2^k)` (`k` the layer's
  half-size exponent) — so the permutation is threaded at all `e` boundaries,
  not only at one.

NOT closed (the precisely-named remaining bookkeeping):

* **the concrete ML-KEM Montgomery twiddle schedule.**  `routedNtt` threads the
  *abstract* twiddle `ω` and its per-layer squarings `ω^2`, `ω^4`, … (the
  Cooley–Tukey twiddle halving), and the routed tree is proved equal to `dft`
  for *any* `ω` with `ω^(2^e) = 1`.  Substituting the concrete ML-KEM Montgomery
  twiddle constants `Nm k`/`Npr k` (so the abstract `ω^j` becomes the stored
  Montgomery-domain twiddle the owned stage reads) is the per-layer constant
  setup named in `MlkemNttFullTie`/`MlkemNttEndToEnd` — supplied per
  layer, not derivable from the abstract `ω`;
* the **per-lane cross-stage register addressing** (which owned ZMM lane of
  stage `k+1` reads which `"zr"` lane of stage `k`) over all 8 stages.  The
  *index permutation* is now fully assembled (the deinterleave is threaded at
  every layer, and its 8-fold composite is the bit-reversal); tying that index
  permutation to the concrete owned-register lane numbering is the same open
  addressing work named in the source files.

So: the **full-depth routed combine tree = abstract `dft 256`** is closed (the
permutation threaded at every layer, not one); the concrete Montgomery twiddle
constants and the owned-register lane addressing remain the named per-layer
setup, handled in the separate machine-realization web.  No
`jasminc_preserves_ct` appears in any theorem here.

## References
* NIST FIPS 203 (ML-KEM); Cooley & Tukey 1965 (radix-2 FFT, bit-reversal).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MlkemNttFullAssembly

open CatCrypt.Crypto.Lattice.NTTRecursionPass
open CatCrypt.Crypto.Optimizer.Lattice.NTTRecursiveFull
open CatCrypt.Crypto.SecureCompilation.MlkemNttPermutation

/-! ## §1  The fully-routed combine tree (deinterleave threaded at every layer) -/

variable {R : Type*} [CommRing R]

/-- The radix-2 Cooley–Tukey butterfly combine `a + ω·b`.  Inlined here (it is a
one-line ring expression over an arbitrary `CommRing`) to keep this fully-abstract
assembly free of any machine-realization import — the owned-lane realization of
this same arithmetic lives in the (separate) realization web. -/
def combine2 (ω a b : R) : R := a + ω * b

/-- The **fully-routed owned combine tree**.  At depth `e+1`, the input `x :
Fin (2^(e+1)) → R` is deinterleaved into its blocked `[evens ‖ odds]` layout
`v = (reindex e x) ∘ deinterleave (2^e)`; the lower `[0,2^e)` and upper
`[2^e,2·2^e)` halves of `v` are each transformed by `routedNtt e (ω^2)` — so the
deinterleave permutation is threaded at *this* layer and, recursively, at every
layer below — and the two half-transforms are butterfly-combined with the owned
`combine2` atom (lower-half twiddle `ω^k`, upper-half twiddle `ω^(2^e)·ω^(k-2^e)`).
The base case `e = 0` is the identity (length-1 transform).  This is the
per-layer routed combine atom of `MlkemNttEndToEnd` iterated to full depth. -/
def routedNtt : (e : ℕ) → R → (Fin (2 ^ e) → R) → (Fin (2 ^ e) → R)
  | 0, _, x => x
  | (e + 1), ω, x => fun k =>
    let v : Fin (2 * 2 ^ e) → R := (reindex e x) ∘ deinterleave (2 ^ e)
    let E := routedNtt e (ω ^ 2) (fun i : Fin (2 ^ e) => v ⟨i.val, by omega⟩)
    let O := routedNtt e (ω ^ 2) (fun i : Fin (2 ^ e) => v ⟨2 ^ e + i.val, by omega⟩)
    if h : k.val < 2 ^ e then
      combine2 (ω ^ k.val) (E ⟨k.val, h⟩) (O ⟨k.val, h⟩)
    else
      E ⟨k.val - 2 ^ e, by
            have hk : k.val < 2 ^ (e + 1) := k.isLt
            have he : (2 : ℕ) ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ]; ring
            omega⟩
        + ω ^ (2 ^ e) * ω ^ (k.val - 2 ^ e)
            * O ⟨k.val - 2 ^ e, by
                have hk : k.val < 2 ^ (e + 1) := k.isLt
                have he : (2 : ℕ) ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ]; ring
                omega⟩

/-! ## §2  The routed tree computes the abstract recursion, at full depth -/

/-- **The fully-routed combine tree equals the abstract recursion.**  By
induction on depth `e`: `routedNtt e ω x = nttRec e ω x`.  The base case `e = 0`
is `rfl`.  The inductive step routes each half through the deinterleave
permutation (`deinterleave_routes_even_odd`) so the lower/upper halves of the
blocked vector are `evenPart`/`oddPart`, and the induction hypothesis rewrites
the two routed sub-trees into the abstract half-transforms; the owned `combine2`
atom is the abstract `E + ω^k·O` butterfly.  This threads the deinterleave at
*every* layer of the descent — the full-depth assembly. -/
theorem routedNtt_eq_nttRec :
    ∀ (e : ℕ) (ω : R) (x : Fin (2 ^ e) → R) (k : Fin (2 ^ e)),
      routedNtt e ω x k = nttRec e ω x k
  | 0, _, _, _ => rfl
  | (e + 1), ω, x, k => by
    -- Abbreviate the deinterleaved blocked vector both definitions use.
    set v : Fin (2 * 2 ^ e) → R := (reindex e x) ∘ deinterleave (2 ^ e) with hv
    -- The two routed half-inputs (lower/upper halves of `v`).
    set lo : Fin (2 ^ e) → R := fun i : Fin (2 ^ e) => v ⟨i.val, by omega⟩ with hlo
    set hi : Fin (2 ^ e) → R := fun i : Fin (2 ^ e) => v ⟨2 ^ e + i.val, by omega⟩
      with hhi
    -- IH: each routed sub-tree equals the abstract recursion at depth `e`.
    have ihlo : ∀ j : Fin (2 ^ e),
        routedNtt e (ω ^ 2) lo j = nttRec e (ω ^ 2) lo j :=
      fun j => routedNtt_eq_nttRec e (ω ^ 2) lo j
    have ihhi : ∀ j : Fin (2 ^ e),
        routedNtt e (ω ^ 2) hi j = nttRec e (ω ^ 2) hi j :=
      fun j => routedNtt_eq_nttRec e (ω ^ 2) hi j
    -- Routing: lower/upper halves of `v` are `evenPart`/`oddPart` of `reindex e x`.
    have hroute := deinterleave_routes_even_odd (2 ^ e) (reindex e x)
    have heven : evenPart (reindex e x) = lo := by
      funext i; rw [hlo]; exact (hroute.1 i).symm
    have hodd : oddPart (reindex e x) = hi := by
      funext i; rw [hhi]; exact (hroute.2 i).symm
    -- Unfold both sides to their butterfly shape and route by the half split.
    show (if h : k.val < 2 ^ e then
            combine2 (ω ^ k.val) (routedNtt e (ω ^ 2) lo ⟨k.val, h⟩)
              (routedNtt e (ω ^ 2) hi ⟨k.val, h⟩)
          else
            routedNtt e (ω ^ 2) lo ⟨k.val - 2 ^ e, _⟩
              + ω ^ (2 ^ e) * ω ^ (k.val - 2 ^ e)
                * routedNtt e (ω ^ 2) hi ⟨k.val - 2 ^ e, _⟩)
        = (if h : k.val < 2 ^ e then
            nttRec e (ω ^ 2) (evenPart (reindex e x)) ⟨k.val, h⟩
              + ω ^ k.val * nttRec e (ω ^ 2) (oddPart (reindex e x)) ⟨k.val, h⟩
          else
            nttRec e (ω ^ 2) (evenPart (reindex e x)) ⟨k.val - 2 ^ e, _⟩
              + ω ^ (2 ^ e) * ω ^ (k.val - 2 ^ e)
                * nttRec e (ω ^ 2) (oddPart (reindex e x)) ⟨k.val - 2 ^ e, _⟩)
    rw [heven, hodd]
    by_cases h : k.val < 2 ^ e
    · rw [dite_eq_left h, dite_eq_left h, combine2, ihlo, ihhi]
    · rw [dite_eq_right h, dite_eq_right h, ihlo, ihhi]

/-! ## §3  The routed tree computes the abstract `dft`, at full depth -/

/-- **The fully-routed combine tree computes `dft (2^e)`.**  Composing
`routedNtt_eq_nttRec` (routed tree = abstract recursion) with `nttRec_eq_dft`
(abstract recursion = `dft`): for any depth `e` whose twiddle is a `2^e`-th root
of unity, the routed owned combine tree — deinterleave permutation threaded at
every layer — computes the abstract length-`2^e` transform `dft (2^e)`. -/
theorem routedNtt_eq_dft (e : ℕ) (ω : R) (hω : ω ^ (2 ^ e) = 1)
    (x : Fin (2 ^ e) → R) (k : Fin (2 ^ e)) :
    routedNtt e ω x k = dft (2 ^ e) ω x k := by
  rw [routedNtt_eq_nttRec e ω x k, nttRec_eq_dft e ω hω x k]

/-! ## §4  Headline: the 8-layer routed owned tree IS `dft 256` -/

/-- **The 8-layer routed owned combine tree is the ML-KEM `dft 256`.**  At depth
`e = 8` (so `2^8 = 256`), the fully-routed combine tree — with the deinterleave
permutation threaded between *all 8 layers* — computes the abstract ML-KEM-length
transform `dft 256`, for any twiddle `ω` that is a `256`-th root of unity.  This
is the full-depth assembly: the per-layer routed tie of `MlkemNttEndToEnd`
iterated across the complete `log₂ 256 = 8` layers, the permutation appearing at
every layer (not one boundary). -/
theorem routedNtt256_eq_dft256 (ω : R) (hω : ω ^ (256 : ℕ) = 1)
    (x : Fin 256 → R) (k : Fin 256) :
    routedNtt 8 ω x k = dft 256 ω x k := by
  have hω' : ω ^ (2 ^ 8 : ℕ) = 1 := by norm_num; exact hω
  have h := routedNtt_eq_dft 8 ω hω' x k
  simpa using h

end CatCrypt.Crypto.SecureCompilation.MlkemNttFullAssembly
