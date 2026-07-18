/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHaxLeaves
import CatCrypt.Crypto.SecureCompilation.CompileFromHaxKeccak
import CatCrypt.Crypto.SecureCompilation.CompileFromHaxBlake2

/-!
# C5: the ONE generic emit-validator that subsumes the per-leaf C KAT

The C4 leaves (`CompileFromHaxLeaves`, `…Keccak`, `…Blake2`, `…Sha512`,
`…Poseidon2`, `…Hmac`) each carry a bespoke `*_compiles` theorem that re-threads
the same boilerplate: `set` the compiled `Com` from an `isSome`, recover the
`some` equation, and route a per-leaf source-spec lemma through the C3
per-primitive obligation `CompileFromHax.compileFromHax_meets_spec`. That
boilerplate is precisely the **emit-validator** the per-leaf C KAT harness used
to play the role of — "does the emitted artifact compute the FIPS / RFC spec?".

This module factors that boilerplate into a **single generic validator**, so
"this leaf is emit-validated against its spec" becomes a uniform one-liner.

## The generic predicate and its discharge

* `LeafValidated params src spec` (`§1`) is the generic *emit = spec* predicate:
  there is a compiled `Com jasminDialect` `c` with `compileFromHax params src =
  some c`, and for *every* input vector `I`, `c.denote (inputValuation w nIn I)`
  equals the reference `spec I`. The reference **is** the FIPS / NIST / RFC spec
  value — `LeafValidated` says the verified compiler's output matches it.

* `leafValidated_of_src_spec` (`§2`) is the **one generic validator**: given
  (a) the compile succeeds (`compileFromHax … |>.isSome`), and (b) the *source*
  denotation of `src` equals `spec` at every input
  (`∀ I, ImpExpr.denoteScalar params I src (LEnv.empty w) = some (spec I)`), it
  discharges `LeafValidated`. The whole compiler-correctness argument is the C3
  meta-theorem (`compileFromHax_meets_spec`), invoked once here; per-leaf there
  is **no compiler reasoning** — only the source-spec agreement obligation a leaf
  author already proves as `*_src_denote` / `*Src_denoteScalar`.

`ValidatedLeaf` (`§1`) bundles the same data as a structure for a packaged form.

## §3 — the per-leaf C KAT is now a Lean theorem, uniformly

The `example`s in `§3` instantiate `LeafValidated` on existing C4 leaves across
three primitive families — SHA-256 `Σ₀` (`bigSigma0`), Keccak `χ`-lane
(`chiLane`), and BLAKE2s `G` (`blake2G`) — each as a single application of
`leafValidated_of_src_spec` reusing the leaf's *existing* `isSome` and
`*Src_denoteScalar` lemmas. No per-leaf compiler reasoning; the bespoke
`*_compiles` proof script is replaced by the uniform validator.

## Relation to the C KAT (subsumption)

The per-leaf C KAT cross-checked a *finite* set of input vectors against the
reference at the byte level. `LeafValidated` is **strictly stronger**: it is a
Lean proof that the emitted `Com`'s denotation equals the spec for *all* inputs
`I`, not a finite sample. The finite C KAT is therefore *subsumed* — any vector
it would test is an instance of the universally-quantified equation.

What remains a **separate** concern (deliberately *not* built here) is the
external, byte-level cross-check of the *TCB printer*: `LeafValidated` validates
the `Com` *denotation* against the spec, but the trusted pretty-printer that
emits the final assembly/C text from that `Com` is outside this denotational
statement. That printer-output cross-check stays a distinct artifact.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxValidator

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)

/-! ## §1  The generic *emit = spec* predicate -/

/-- **The generic emit-validation predicate.** A leaf with hax source `src`,
    parameter list `params`, and reference spec `spec : (Fin nIn → BitVec w) →
    BitVec w` is *validated* when the verified compiler emits a `Com jasminDialect`
    `c` from `src` and that `c`'s denotation equals `spec` at every input vector.

    The reference **is** the FIPS / NIST / RFC spec: `LeafValidated` is the Lean
    statement that the verified compiler's output meets it — for *all* inputs,
    subsuming any finite per-leaf C KAT. -/
def LeafValidated {w nIn : Nat} (params : List String) (src : ImpExpr)
    (spec : (Fin nIn → BitVec w) → BitVec w) : Prop :=
  ∃ c : Com jasminDialect (frontCtxt w nIn []) (rW w),
    compileFromHax params src = some c ∧
    ∀ I : Fin nIn → BitVec w, c.denote (inputValuation w nIn I) = spec I

/-- Packaged form of a validated leaf: the params, source, reference spec, and the
    two proof obligations (`compile-succeeds` and `source-meets-spec`) bundled
    into one structure. `ValidatedLeaf.validated` discharges `LeafValidated` from
    the bundle via the generic validator `leafValidated_of_src_spec`. -/
structure ValidatedLeaf (w nIn : Nat) where
  /-- The hax extraction parameter names. -/
  params : List String
  /-- The extracted hax source expression (let-normalized `ImpExpr`). -/
  src : ImpExpr
  /-- The FIPS / NIST / RFC reference spec the leaf must compute. -/
  spec : (Fin nIn → BitVec w) → BitVec w
  /-- The compile-from-hax pipeline succeeds on `src`. -/
  isSome : (compileFromHax (w := w) (nIn := nIn) params src).isSome
  /-- The *source* denotation of `src` equals the reference spec at every input —
      the single source-level obligation a leaf author proves (`*Src_denoteScalar`). -/
  srcSpec : ∀ I : Fin nIn → BitVec w,
    ImpExpr.denoteScalar params I src (LEnv.empty w) = some (spec I)

/-! ## §2  The one generic validator (discharge via the C3 meta-theorem) -/

/-- **The single generic emit-validator.** Given that the compile succeeds and the
    *source* denotation of `src` matches the reference `spec` at every input, the
    emitted `Com`'s denotation matches `spec` — i.e. `LeafValidated` holds. The
    whole compiler-correctness argument routes through the C3 per-primitive
    obligation `compileFromHax_meets_spec` exactly once; there is **no per-leaf
    compiler reasoning**. This is the uniform replacement for the bespoke
    `*_compiles` script and for the per-leaf C KAT. -/
theorem leafValidated_of_src_spec {w nIn : Nat} (params : List String)
    (src : ImpExpr) (spec : (Fin nIn → BitVec w) → BitVec w)
    (hSome : (compileFromHax (w := w) (nIn := nIn) params src).isSome)
    (hSrc : ∀ I : Fin nIn → BitVec w,
      ImpExpr.denoteScalar params I src (LEnv.empty w) = some (spec I)) :
    LeafValidated (w := w) (nIn := nIn) params src spec := by
  -- The emitted `Com` is computed by the compiler; `hSome` proves it is `some`.
  set c := (compileFromHax (w := w) (nIn := nIn) params src).get hSome with hc_def
  have hc : compileFromHax (w := w) (nIn := nIn) params src = some c :=
    (Option.some_get _).symm
  refine ⟨c, hc, ?_⟩
  intro I
  -- Route the per-input source-spec through the C3 per-primitive obligation:
  -- all compiler correctness lives in `compileFromHax_meets_spec`.
  exact compileFromHax_meets_spec (w := w) (nIn := nIn) params I src (spec I) hc (hSrc I)

/-- A `ValidatedLeaf` bundle discharges `LeafValidated` via the generic validator. -/
theorem ValidatedLeaf.validated {w nIn : Nat} (L : ValidatedLeaf w nIn) :
    LeafValidated (w := w) (nIn := nIn) L.params L.src L.spec :=
  leafValidated_of_src_spec L.params L.src L.spec L.isSome L.srcSpec

/-! ## §3  Instantiation on existing compiler-derived leaves

Each `example` validates an existing C4 leaf as a *single* application of
`leafValidated_of_src_spec`, reusing the leaf's already-proven `isSome` and
`*Src_denoteScalar` lemmas — no new compiler reasoning, no per-leaf KAT. The
bespoke `*_compiles` proof script is fully subsumed by the generic validator.

We instantiate across three primitive families to show uniformity:
SHA-256 (`bigSigma0`), Keccak (`chiLane`), and BLAKE2s (`blake2G`). -/

open CatCrypt.Crypto.SecureCompilation.CompileFromHaxLeaves
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxKeccak
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxBlake2

/-- **SHA-256 `Σ₀` is emit-validated** (FIPS 180-4): the compiler-emitted `Com`
    denotes to `(x ror 2) ⊕ (x ror 13) ⊕ (x ror 22)` for all `x`. A one-liner via
    the generic validator, reusing `bigSigma0_compileFromHax_isSome` and
    `bigSigma0Src_denoteScalar`. -/
example :
    LeafValidated (w := 32) (nIn := 1) ["x"] bigSigma0Src
      (fun I => (I 0).rotateRight 2 ^^^ (I 0).rotateRight 13 ^^^ (I 0).rotateRight 22) :=
  leafValidated_of_src_spec ["x"] bigSigma0Src _
    bigSigma0_compileFromHax_isSome
    bigSigma0Src_denoteScalar

/-- **Keccak `χ`-lane is emit-validated** (FIPS 202): the compiler-emitted `Com`
    denotes to `a0 ⊕ ((¬a1) ∧ a2)` for all inputs. A one-liner via the generic
    validator, reusing `chiLane_compileFromHax_isSome` and `chiLaneSrc_denoteScalar`. -/
example :
    LeafValidated (w := 32) (nIn := 3) ["a0", "a1", "a2"] chiLaneSrc
      (fun I => inpGet I 0 ^^^ ((~~~ inpGet I 1) &&& inpGet I 2)) :=
  leafValidated_of_src_spec ["a0", "a1", "a2"] chiLaneSrc _
    chiLane_compileFromHax_isSome
    chiLaneSrc_denoteScalar

/-- **BLAKE2s `G` output word is emit-validated** (RFC 7693): the compiler-emitted
    `Com` denotes to `blake2GSpec` for all inputs. A one-liner via the generic
    validator, reusing `blake2G_compileFromHax_isSome` and `blake2GSrc_denoteScalar`. -/
example :
    LeafValidated (w := 32) (nIn := 6) ["a", "b", "c", "d", "x", "y"] blake2GSrc
      (fun I => blake2GSpec (inpGet I 0) (inpGet I 1) (inpGet I 2) (inpGet I 3)
                  (inpGet I 4) (inpGet I 5)) :=
  leafValidated_of_src_spec ["a", "b", "c", "d", "x", "y"] blake2GSrc _
    blake2G_compileFromHax_isSome
    blake2GSrc_denoteScalar

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxValidator
