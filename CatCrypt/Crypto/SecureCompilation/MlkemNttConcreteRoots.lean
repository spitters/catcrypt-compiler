/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.MlkemNttFullAssembly
import CatCrypt.Crypto.Optimizer.Lattice.ConcreteNttRoots

/-!
# The owned routed NTT tree at the CONCRETE ML-KEM root of unity ζ = 17

`MlkemNttFullAssembly.lean` proved `routedNtt256_eq_dft256`: the 8-layer
routed owned combine tree (deinterleave permutation threaded between *all 8*
layers) equals the abstract length-256 transform `dft 256`, for **any** twiddle
`ω` that is a `256`-th root of unity — i.e. parameterized over an *abstract*
root `ω` with `ω ^ 256 = 1`.

This module instantiates that abstract statement at the **concrete ML-KEM root**
`ζ = 17 : ZMod 3329`.  ML-KEM works in `ZMod 3329` with polynomial degree
`n = 256`; the standard NTT root is `ζ = 17`, a primitive `256`-th root of unity
(`3329 - 1 = 2^8 · 13`, so `256 ∣ 3329 - 1`).  The core number-theory fact
`(17 : ZMod 3329) ^ 256 = 1` is **already proved** in
`ConcreteNttRoots.pow_256_17_eq_one` (and `17` is shown a *primitive* 256-th root
in `isPrimitiveRoot_17_256`).  We reuse it verbatim — no number theory is
re-derived here.

## What this module ADDS

* **`mlkem_routedNtt256_eq_dft256`** — the headline: the 8-layer routed owned
  combine tree, evaluated at the **actual ML-KEM zeta `17 : ZMod 3329`**, equals
  the ML-KEM-specification transform `dft 256 (17 : ZMod 3329)`.  The abstract
  root-of-unity hypothesis `ω ^ 256 = 1` is discharged by the existing
  primitive-root computation `pow_256_17_eq_one`.

* **`mlkem_routedNtt_eq_dft`** — the same instantiation at *every* depth `e` for
  which the per-layer twiddle squaring keeps `17` a `2^e`-th root.  We state the
  full-depth case (`e = 8`, the only depth needed for ML-KEM-256) and the generic
  one is `routedNtt_eq_dft` already.

## Scope — what this instantiation closes, what remains

CLOSED here (the abstract-root substitution):

* the routed combine tree, **specialized to the real ML-KEM ring `ZMod 3329`
  and the real ML-KEM root `ζ = 17`**, computes the ML-KEM `dft 256`.  The
  abstract `ω` of `MlkemNttFullAssembly` is now the concrete ML-KEM zeta;
  the root-of-unity side condition is discharged by the proved primitive-root
  fact, not assumed.

REMAINING (a separate, machine-level concern — NOT addressed here):

* the **Montgomery-operand-form twiddle constants.**  `routedNtt` threads the
  *abstract field element* `ω ^ j` (here `17 ^ j : ZMod 3329`) as each layer's
  twiddle.  The owned ZMM stage reads its twiddle as a *Montgomery-domain*
  `BitVec 64` operand (`Nm k` / `Npr k`), i.e. `17 ^ j · R mod 3329` in machine
  form.  Substituting those stored Montgomery operands for the abstract
  `17 ^ j`, and tying the per-lane cross-stage owned-register addressing, is the
  machine-wiring step named in `MlkemNttFullAssembly`'s header.  It is a
  *representation* change (field element ↔ stored Montgomery `BitVec`), not the
  abstract-root substitution done here.

So: the owned routed tree, at the **actual ML-KEM zeta**, computes the ML-KEM
spec `dft 256`.  The Montgomery-operand encoding of the per-layer twiddles
remains machine wiring.  No `jasminc_preserves_ct` appears in any theorem here.

The instantiation inherits the `native_decide` evaluation of `17 ^ 256 = 1`
from `pow_256_17_eq_one` (the proved primitive-root fact), so the headline's
axiom set includes the kernel reduction axiom `Lean.ofReduceBool` from that
computation — reported below, inherited from the existing
number-theory proof.

## References
* NIST FIPS 203 (ML-KEM); `3329 - 1 = 2^8 · 13`; Cooley & Tukey 1965.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MlkemNttConcreteRoots

open CatCrypt.Crypto.Optimizer.Lattice.NTTRecursionPass (dft)
open CatCrypt.Crypto.SecureCompilation.MlkemNttFullAssembly (routedNtt routedNtt_eq_dft routedNtt256_eq_dft256)
open CatCrypt.Crypto.Optimizer.Lattice.ConcreteNttRoots (pow_256_17_eq_one isPrimitiveRoot_17_256)

/-! ## §1  The headline: owned routed tree at the real ML-KEM root = ML-KEM `dft 256` -/

/-- **The 8-layer routed owned combine tree, at the ACTUAL ML-KEM root
`ζ = 17 : ZMod 3329`, computes the ML-KEM-specification `dft 256`.**

This instantiates the abstract-root statement `routedNtt256_eq_dft256` of
`MlkemNttFullAssembly` at the concrete ML-KEM zeta.  The abstract
root-of-unity side condition `ω ^ 256 = 1` is discharged by the **existing**
primitive-root computation `ConcreteNttRoots.pow_256_17_eq_one`
(`(17 : ZMod 3329) ^ 256 = 1`) — no number theory is re-derived.

What is closed: the routed combine tree, specialized to the real ML-KEM ring
`ZMod 3329` and root `17`, equals the ML-KEM `dft 256`.  What remains (machine
wiring, see header): the Montgomery-operand encoding of the per-layer twiddle
constants `17 ^ j · R mod 3329`. -/
theorem mlkem_routedNtt256_eq_dft256
    (x : Fin 256 → ZMod 3329) (k : Fin 256) :
    routedNtt 8 (17 : ZMod 3329) x k = dft 256 (17 : ZMod 3329) x k :=
  routedNtt256_eq_dft256 (17 : ZMod 3329) pow_256_17_eq_one x k

/-- **Full-depth (`e = 8`) instantiation via `routedNtt_eq_dft` at the concrete
root.**  Same content as `mlkem_routedNtt256_eq_dft256`, routed through the
depth-generic `routedNtt_eq_dft` (`2^8 = 256`), making explicit that the
discharged hypothesis is exactly `(17 : ZMod 3329) ^ (2^8) = 1`, the proved
primitive-root fact `pow_256_17_eq_one`. -/
theorem mlkem_routedNtt_eq_dft
    (x : Fin (2 ^ 8) → ZMod 3329) (k : Fin (2 ^ 8)) :
    routedNtt 8 (17 : ZMod 3329) x k = dft (2 ^ 8) (17 : ZMod 3329) x k :=
  routedNtt_eq_dft 8 (17 : ZMod 3329)
    (by show (17 : ZMod 3329) ^ (256 : ℕ) = 1; exact pow_256_17_eq_one) x k

/-! ## §2  Re-export the primitive-root provenance -/

/-- The concrete ML-KEM root `17` is a *primitive* `256`-th root of unity in
`ZMod 3329` (re-exported from `ConcreteNttRoots.isPrimitiveRoot_17_256`).  This
is the provenance of the root used in `mlkem_routedNtt256_eq_dft256`: `17` is the
primitive `256`-th root (not just *a* root), so the routed tree at `17`
computes the (non-degenerate) ML-KEM transform. -/
theorem mlkem_root_isPrimitive : IsPrimitiveRoot (17 : ZMod 3329) 256 :=
  isPrimitiveRoot_17_256

end CatCrypt.Crypto.SecureCompilation.MlkemNttConcreteRoots
