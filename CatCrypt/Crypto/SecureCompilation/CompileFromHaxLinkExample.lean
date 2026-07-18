/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHaxLink

/-!
# C8 worked example: the Mode-A two-front combiner on a SHA-256 σ₀ leaf

`CompileFromHaxLink.lean` builds the registry/linker machinery and a *toy* worked
example whose leaf (`"f"`, `spec x = x + x`) is a stand-in. This module promotes
that to a **realistic worked example**: a registry-resolved SHA-256
message-schedule σ₀ leaf, linked into a compile-from-hax-shaped outer, composed
into one whole-primitive correctness theorem.

## The two fronts, met at one `extCall`

* **Outer (compile-from-hax front).** A small `Com jasminDialect` produced by the
  verified front (`ThirToComFront`) from a one-statement THIR
  `let r = sha256_sigma0(inp[0]); ret r`. This is the *outer* authoring front: a
  straight-line scalar body (here trivial) surrounding **one `extCall` boundary**
  to the fast leaf. Its denotation is pinned to `jasminExtSem "sha256_sigma0" …`
  of the input — the opaque external-call value (`outerSigma0Com_denote_opaque`),
  exactly the `compileFromHax`-style outer obligation: correct *relative to* the
  call.
* **Leaf (author-in-Com fast front).** A `LeafSpec 32` keyed under
  `"sha256_sigma0"` whose `spec` is the FIPS 180-4 σ₀ formula
  `(x ror 7) ⊕ (x ror 18) ⊕ (x >> 3)`. Its per-leaf agreement
  `jasminExtSem "sha256_sigma0" … = spec` is the fast author's obligation — a
  **hypothesis**, not an axiom (`jasminExtSem "sha256_sigma0"` is opaque, the
  `_, _, retTy => default` arm), standing for the validated σ₀-leaf KAT /
  rotate-xor kernel correctness.

## What is mechanized vs. the carried obligation

* **Mechanized (this file):** the *composition*. `linkedExample_correct` rewrites
  the outer's opaque-call denotation (`outerSigma0Com_denote_opaque`, proved
  through the front's value-preservation `thirToJasmin_denote`) by the leaf's
  agreement (`extCall_denote_via_leaf` / the registered `LeafSpec.agrees`), and
  computes the σ₀ formula. Two fronts → one whole-primitive `*_correct` theorem.
* **The carried obligation (hypothesis):** the per-leaf agreement `hagree`. It is
  *threaded once* into the `LeafSpec.agrees` field of the registered leaf, and
  every theorem that links against that leaf inherits it — the C8 contract: the
  per-leaf proof is discharged once per leaf, inherited by every caller.

## Scope: single-`extCall` worked example

This example has **one** leaf boundary (one `extCall`). It demonstrates the
combiner end to end. The remaining generalization is the **N-call walk**:
recursing `extCall_denote_via_leaf` over *every* `extCall` node of an arbitrary
outer `Com`, driven by `linkNames`/`LeafRegistry` (the fold skeleton already in
`CompileFromHaxLink.§4`). The single-boundary case here is the acceptable C8
deliverable and the inductive base of that walk.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxLinkExample

open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxLink

/-! ## §1  The registered leaf: SHA-256 σ₀

The fast leaf is the SHA-256 message-schedule σ₀ word permutation. Its arity is
1 (one 32-bit input word), its `spec` is the FIPS 180-4 formula, and it is keyed
under the external-call name `"sha256_sigma0"` — the name the outer's `extCall`
boundary targets. -/

/-- The external-call name of the σ₀ fast leaf. -/
def sigma0Name : String := "sha256_sigma0"

/-- The FIPS 180-4 SHA-256 σ₀ word permutation as a 1-argument `BitVec 32` spec:
    `σ₀(x) = (x ror 7) ⊕ (x ror 18) ⊕ (x >> 3)`. The intended semantics of the
    registered leaf. -/
def specSigma0 : (Fin 1 → BitVec 32) → BitVec 32 :=
  fun a => (a 0).rotateRight 7 ^^^ (a 0).rotateRight 18 ^^^ (a 0) >>> (3 : Nat)

/-! ## §2  The outer: a compile-from-hax-shaped `Com` with one `extCall`

The outer is the front's lowering of `let r = sha256_sigma0(inp[0]); ret r` — a
straight-line scalar body whose single right-hand side is the `extCall` boundary
to the σ₀ leaf. (Mirrors the toy `outerThir`/`outerCom` of `CompileFromHaxLink`,
retargeted to the realistic σ₀ leaf name.) -/

/-- The outer THIR: `let r = sha256_sigma0(inp[0]); ret r`. One single-argument
    external call to the σ₀ leaf, returning its result. -/
def outerSigma0Thir : Thir :=
  .let_ "r" (.call sigma0Name [.inp 0]) (.ret (.lvar "r"))

/-- The outer lowers (the front returns `some`) at width 32 with `nIn = 1`: the
    one argument `inp 0` resolves to input word 0, so `rhsExpr (.call …)` and the
    `ret` both succeed. -/
theorem outerSigma0Thir_lowers :
    (thirToJasmin (w := 32) (nIn := 1) [] (initFState 32 1) outerSigma0Thir).isSome := by
  simp only [outerSigma0Thir, thirToJasmin, rhsExpr, atomsToVarHV, Atom.toVar,
    initFState, FState.push, inputVarRep, Option.map_some, if_true]
  rfl

/-- The outer `Com` (the front's output) at width 32. -/
def outerSigma0Com : Com jasminDialect (frontCtxt 32 1 []) (rW 32) :=
  (thirToJasmin (w := 32) (nIn := 1) [] (initFState 32 1) outerSigma0Thir).get
    outerSigma0Thir_lowers

/-- **Outer value-preservation, relative to the opaque call.** For any input `x`,
    the compiled outer `Com` denotes to `jasminExtSem "sha256_sigma0" …` of `x` —
    the opaque external-call value, *before* linking. This is the
    `compileFromHax`-style outer obligation, proved through the front's
    value-preservation `thirToJasmin_denote`: the outer is correct *relative to*
    the σ₀ call. -/
theorem outerSigma0Com_denote_opaque (x : BitVec 32) :
    outerSigma0Com.denote (inputValuation 32 1 (fun _ => x))
      = jasminExtSem sigma0Name (callArgTys 32 1) (rW 32)
          (HVector.cons (x : ⟦rW 32⟧) HVector.nil) := by
  have hc : thirToJasmin (w := 32) (nIn := 1) [] (initFState 32 1) outerSigma0Thir
      = some outerSigma0Com := (Option.some_get _).symm
  have hfront := thirToJasmin_denote (w := 32) (nIn := 1) []
    (fun _ => x) outerSigma0Thir (LEnv.empty 32) (initFState 32 1)
    (inputValuation 32 1 (fun _ => x)) outerSigma0Com (initAgree (fun _ => x)) hc
  have hthir : Thir.denote (w := 32) (nIn := 1) (fun _ => x) outerSigma0Thir (LEnv.empty 32)
      = some (jasminExtSem sigma0Name (callArgTys 32 1) (rW 32)
          (HVector.cons (x : ⟦rW 32⟧) HVector.nil)) := by
    have hx : inpGet (nIn := 1) (fun _ => x) 0 = x := by
      simp only [inpGet, show (0 : Nat) < 1 by decide, dif_pos]
    simp only [outerSigma0Thir, Thir.denote, Rhs.denote, atomsHV, Atom.denote, hx,
      Option.bind_some, Option.map_some, LEnv.set, if_pos]
    rfl
  rw [hthir] at hfront
  exact (Option.some.injEq _ _ ▸ hfront).symm

/-! ## §3  The registry and the linked whole-primitive theorem

The registry holds exactly the σ₀ leaf (its `agrees` field is the carried
hypothesis `hagree`). `linkedExample_correct` composes the two fronts: the
outer's opaque-call value-preservation (`outerSigma0Com_denote_opaque`) and the
leaf agreement (`hagree`, the registered `LeafSpec.agrees`) into one statement —
the compiled outer denotes to the FIPS σ₀ value. -/

/-- The registry holding exactly the σ₀ leaf, keyed under `"sha256_sigma0"`. Its
    `agrees` is the carried hypothesis `hagree` — the fast author's per-leaf
    obligation — threaded once into the `LeafSpec.agrees` field. -/
def sigma0Registry
    (hagree : ∀ (args : HVector (fun t => ⟦t⟧) (callArgTys 32 1)),
        (jasminExtSem sigma0Name (callArgTys 32 1) (rW 32) args : ⟦rW 32⟧)
          = specSigma0 (hvToFun args)) :
    LeafRegistry 32 :=
  (LeafRegistry.empty 32).insert
    { name := sigma0Name, n := 1, spec := specSigma0, agrees := hagree }

/-- The σ₀ registry resolves `"sha256_sigma0"` to the σ₀ leaf — the registry side
    of the composition (the call is linkable). -/
theorem sigma0Registry_resolves
    (hagree : ∀ (args : HVector (fun t => ⟦t⟧) (callArgTys 32 1)),
        (jasminExtSem sigma0Name (callArgTys 32 1) (rW 32) args : ⟦rW 32⟧)
          = specSigma0 (hvToFun args)) :
    Resolves (sigma0Registry hagree) sigma0Name
      { name := sigma0Name, n := 1, spec := specSigma0, agrees := hagree } :=
  insert_resolves (LeafRegistry.empty 32) _

/-- **The linked worked example — the Mode-A two-front combiner.** *Given* the
    per-leaf σ₀ agreement `hagree` (the fast author's obligation, carried as the
    registered `LeafSpec.agrees` — a hypothesis, not an axiom, since
    `jasminExtSem "sha256_sigma0"` is opaque), the whole compiled outer's
    denotation is the **FIPS 180-4 σ₀ value** `(x ror 7) ⊕ (x ror 18) ⊕ (x >> 3)`
    for every input `x`.

    The outer's value-preservation (`outerSigma0Com_denote_opaque`, compile-from-hax
    front) is composed with the registered leaf's agreement (`hagree`, author-in-Com
    front) into one whole-primitive `*_correct` statement: the registry+linker has
    turned the opaque-call outer into a spec-defined σ₀ kernel. The per-leaf
    obligation is discharged once (here, supplied as `hagree`) and inherited by
    this and every other caller of the σ₀ leaf. -/
theorem linkedExample_correct
    (hagree : ∀ (args : HVector (fun t => ⟦t⟧) (callArgTys 32 1)),
        (jasminExtSem sigma0Name (callArgTys 32 1) (rW 32) args : ⟦rW 32⟧)
          = specSigma0 (hvToFun args))
    (x : BitVec 32) :
    outerSigma0Com.denote (inputValuation 32 1 (fun _ => x))
      = x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ x >>> (3 : Nat) := by
  -- Step 1 (mechanized): outer value-preservation relative to the opaque call.
  rw [outerSigma0Com_denote_opaque x]
  -- Step 2 (the carried leaf obligation): link the opaque call to the σ₀ spec.
  rw [hagree (HVector.cons (x : ⟦rW 32⟧) HVector.nil)]
  -- Step 3 (compute): `specSigma0` of the single argument `x` is the FIPS formula.
  show specSigma0 (hvToFun (HVector.cons (x : ⟦rW 32⟧) HVector.nil))
      = x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ x >>> (3 : Nat)
  simp only [specSigma0, hvToFun, hvNth, Fin.cases_zero]
  rfl

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxLinkExample
