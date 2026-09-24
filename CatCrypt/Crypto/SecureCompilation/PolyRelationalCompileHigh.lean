/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.RelationalCompileHigh
public import CatCrypt.Crypto.SecureCompilation.RelationalCompileHigh
public meta import CatCrypt.Crypto.SecureCompilation.VIR.PolyDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.PolyDialect
public meta import CatCrypt.Crypto.Optimizer.Lattice.NTTButterflyPass
public import CatCrypt.Crypto.Optimizer.Lattice.NTTButterflyPass

/-!
# A relational-compilation layer over the POLY dialect (`polyDialect`)

This module is the **Poly-dialect** analogue of `RelationalCompileHigh.lean`
(the `FieldDialect` relational engine). Where that engine assembles "the emitted
`Com fieldDialect` program denotes its spec" proofs over the prime-field /
extension-tower op set (`FieldOp`), this engine assembles the same proofs over
the **polynomial-ring op set** (`PolyDialect.PolyOp`: `ntt`/`intt`/`basemul`/
`polyAdd`/`polySub`/`polySMul`/`nttMul`), whose denotation is the abstract
polynomial-ring value (the CompPoly NTT operations over
`CPolynomial (ZMod q)` / `Array (ZMod q)`).

This unlocks the largest *authorable* crypto family: the lattice NTT kernels
(ML-KEM / ML-DSA / HAWK / Plonky3). Rather than hand-authoring an NTT kernel as
a `Com jasminDialect` register schedule, an author writes the kernel as an
**algebraic SPEC over the polynomial ring** and *relationally compiles* it to
`Com polyDialect` here — the highest dialect for the lattice family — and only
then regular-compiles down (`PolyLowering → Field/ModArith → … → jasmin`, the
verified descent).

## The substrate is shared — the engine is dialect-polymorphic

The `RelationalCompileHigh` machinery (`FView`/`FStateStep`/`FRefines`/`bindOp`/
`fieldOp`/`seq`/`skip`) only uses the `Com`/`Expr`/`Ctxt`/`DialectDenote`
substrate from `VIR.Core` — *none* of it is `fieldDialect`-specific except the
instantiation. The Poly engine below is therefore the **same** De-Bruijn
valuation-threading layer, re-instantiated at `polyDialect`:

* `PView Γ := Ctxt.Valuation Γ` — the abstract machine state is the valuation
  (of polynomial-ring values).
* `PStateStep Γ Δ := PView Γ → PView Δ` — a step pushes the poly value computed
  by one op.
* `PRefines spec frag` says the CPS fragment `frag` denotes its continuation
  applied to the spec-transformed valuation. (The high-dialect `Com.denote` is
  exact, so the low engine's existential collapses to a clean equality.)

## What is proved

* `PRefines.polyOp` — the atomic compilation lemma: a single `bindOp` fragment
  refines `pOpStep`. (The Poly analogue of `FRefines.fieldOp`; `rfl` because the
  Poly `Com.denote` *is* the valuation extension.)
* `PRefines.seq` — the composition rule: sequencing two op-fragments composes
  their state-steps.
* `PRefines.skip` — the identity/base case.

## Demonstration A (poly level): the `nttMul` rewrite, authored via the engine

The headline lattice-ring identity
`poly_mul a b = intt (basemul (ntt a) (ntt b))` is *authored* through the
engine's `bindOp`/`seq` builders as a four-binding `Com polyDialect`, and proved
(via the assembled `polyOp`+`seq` lemmas) to refine its composite poly-op
state-step. Because `polyDenote` is `noncomputable` (CompPoly over `ZMod q`,
`Array`-based), this is verified by denote-equality at the dialect, NOT by
`#eval`.

## Demonstration B (butterfly leaf, with `#eval`): one Cooley–Tukey butterfly

A single radix-2 NTT butterfly `(a, b) ↦ (a + ζ·b, a − ζ·b)` over `ZMod q` is the
*leaf* the whole NTT schedule is built from (`PolyLowering.ctButterfly`). It is a
scalar field computation — `fMul`, `fAdd`, `fSub` over `ZMod q` — so it is
authored through the **FieldDialect** engine (`RelationalCompileHigh.bindOp`/
`seq`) at the ML-KEM modulus `q = 3329`, producing a `Com fieldDialect` that
denotes to the abstract butterfly spec `ctButterfly`, with a SMALL `#eval`-safe
single-residue check.

The architecture splits as follows: the Poly engine refines whole-NTT
*polynomial-ring* programs; the butterfly is the *scalar leaf* below them,
authored at the field level. The two engines share the same dialect-polymorphic
substrate.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.PolyRelationalCompileHigh

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.PolyDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeNTTSemantic (NttDomains)
open CompPoly (CPolynomial)

/-! ## 1. Views and state-steps over the Poly dialect

The high-dialect "machine view" is the De Bruijn valuation itself: the list of
polynomial-ring values currently in scope. A fragment that emits one op pushes
that op's result onto the view (at De Bruijn index `0`). This is the exact
analogue of `RelationalCompileHigh.FView`/`FStateStep`, re-indexed at
`polyDialect`. -/

section Engine

variable [ND : NttDomains]

/-- The abstract machine view at context `Γ`: the valuation of all polynomial
    values currently in scope. (The Poly-dialect counterpart of the field
    engine's `FView`.) -/
abbrev PView (Γ : Ctxt polyDialect) : Type := Ctxt.Valuation Γ

/-- A `PStateStep Γ Δ` is what an emitted poly-op fragment does to the abstract
    view: it consumes the in-scope valuation at `Γ` and produces a valuation at
    the *output* context `Δ` (the context after the fragment's bindings —
    `Δ = t :: Γ` for one op, growing further as ops are sequenced). -/
abbrev PStateStep (Γ Δ : Ctxt polyDialect) : Type :=
  PView Γ → PView Δ

/-- The atomic state-step of binding op `op` applied to argument variables
    `args`: push `op`'s abstract poly-ring denotation (read through the current
    view) onto the valuation. This is exactly the spec of `Com.var …` — and
    equals what the Poly `Com.denote` does on that binding. -/
noncomputable def pOpStep {Γ : Ctxt polyDialect} (op : PolyOp)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
              (DialectSignature.sig (d := polyDialect) op)) :
    PStateStep Γ (DialectSignature.ret (d := polyDialect) op :: Γ) :=
  fun V => V.extend (DialectDenote.denote (d := polyDialect) op (Expr.lookupArgs args V))

/-! ## 2. The `PRefines` relation (denotational, Poly dialect)

`PRefines spec frag` says: the CPS fragment `frag`, which binds one poly op and
continues over the extended context, denotes its continuation applied to the
spec-transformed view. Mirrors `RelationalCompileHigh.FRefines`, but over the
`Com polyDialect` substrate. -/

/-- A CPS fragment over `Com polyDialect` from context `Γ` to context `Δ`. For
    one op, `Δ = t :: Γ`; sequencing grows `Δ` further. -/
abbrev PFrag (Γ Δ : Ctxt polyDialect) : Type :=
  {s : PolyTy} → Com polyDialect Δ s → Com polyDialect Γ s

/-- `PRefines spec frag`: the fragment `frag` (from `Γ` to `Δ`) denotes its spec
    `PStateStep Γ Δ`. Because the Poly `Com.denote` is exact
    (`Com.var e body` denotes `body` on `V.extend (e.denote V)`), the advanced
    view is *literally* `spec V`. -/
def PRefines {Γ Δ : Ctxt polyDialect}
    (spec : PStateStep Γ Δ) (frag : PFrag Γ Δ) : Prop :=
  ∀ {s : PolyTy} (V : PView Γ) (k : Com polyDialect Δ s),
    (frag k).denote V = k.denote (spec V)

/-! ## 3. The atomic compilation lemma — `polyOp`

The single-op fragment `bindOp op args` emits one `Com.var` with the poly op and
hands the continuation the extended context. It refines `pOpStep op args`. The
proof is definitional — the Poly `Com.denote` *exactly* extends the valuation by
the op's denotation. -/

/-- The one-op fragment builder: bind `op args` and continue. -/
def bindOp {Γ : Ctxt polyDialect} (op : PolyOp)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
              (DialectSignature.sig (d := polyDialect) op)) :
    PFrag Γ (DialectSignature.ret (d := polyDialect) op :: Γ) :=
  fun k => Com.var (Expr.mk op rfl args) k

/-- **Poly-op compilation lemma** (the atomic refinement). A single `bindOp`
    fragment refines `pOpStep`. Proof: `rfl` — `(Com.var e k).denote V` reduces
    to `k.denote (V.extend (e.denote V))`, and `e.denote V` is exactly the op's
    poly-ring denotation read through `V`, which is precisely `pOpStep op args V`. -/
theorem PRefines.polyOp {Γ : Ctxt polyDialect} (op : PolyOp)
    (args : HVector (fun ty => Ctxt.Var Γ ty) (DialectSignature.sig op)) :
    PRefines (pOpStep op args) (bindOp op args) := by
  intro s V k
  rfl

/-! ## 4. The composition rule — `seq`

Sequencing two op-fragments composes their state-steps. The second fragment
binds onto the context the first produced (`Δ₁`), so it runs `Δ₁ → Δ₂`; the
composite runs `Γ → Δ₂` with spec `spec₂ ∘ spec₁`. -/

/-- **Sequencing compilation lemma** — the composition rule. If `frag₁` refines
    `spec₁` (`Γ → Δ₁`) and `frag₂` refines `spec₂` (`Δ₁ → Δ₂`), then sequencing
    them — `fun k => frag₁ (frag₂ k)` — refines `spec₂ ∘ spec₁` (`Γ → Δ₂`). -/
theorem PRefines.seq {Γ Δ₁ Δ₂ : Ctxt polyDialect}
    {spec₁ : PStateStep Γ Δ₁} {spec₂ : PStateStep Δ₁ Δ₂}
    {frag₁ : PFrag Γ Δ₁} {frag₂ : PFrag Δ₁ Δ₂}
    (h₁ : PRefines spec₁ frag₁) (h₂ : PRefines spec₂ frag₂) :
    PRefines (fun V => spec₂ (spec₁ V)) (fun {s} k => frag₁ (frag₂ k)) := by
  intro s V k
  rw [h₁ V (frag₂ k), h₂ (spec₁ V) k]

/-- **Identity/skip compilation lemma** (the base of a `seq`-fold). The empty
    fragment (apply the continuation directly) refines the identity step. -/
theorem PRefines.skip {Γ : Ctxt polyDialect} :
    PRefines (Γ := Γ) (Δ := Γ) (fun V => V) (fun {s} k => k) := by
  intro s V k
  rfl

end Engine

/-! ## 5. Demonstration A: the `nttMul` rewrite, authored via the engine

The headline lattice-ring identity
`poly_mul a b = intt (basemul (ntt a) (ntt b))` — the rewrite every NTT-using
protocol depends on — is *authored* through the engine's `bindOp` fragment
builders as a four-binding `Com polyDialect`:

    let ta = ntt a                 -- index 0; a,b shift to 1,2
    let tb = ntt b                 -- index 0; ta shifts to 1, a,b to 2,3
    let p  = basemul ta tb         -- index 0
    let c  = intt p
    ret c

Input context `Γ₀ = [polyC q n, polyC q n]` holding `a, b` at De Bruijn indices
`0, 1`. We (1) build it with the engine's `bindOp`, (2) show it refines the
composite poly-op state-step assembled from `polyOp`+`seq`, and (3) prove the
program denotes exactly to `intt (basemul (ntt a) (ntt b))` (= `realNttMul`,
the negacyclic ring product the dialect ties to convolution). -/

namespace NttMulDemo

variable [ND : NttDomains] {q n : Nat}

/-- The starting context: two coefficient-form polynomial inputs `a, b`. -/
abbrev Γ₀ (q n : Nat) : Ctxt polyDialect := [.polyC q n, .polyC q n]

/-- De Bruijn variables for the two inputs `a, b` (indices `0, 1`). -/
def va (q n : Nat) : Ctxt.Var (Γ₀ q n) (.polyC q n) := .here
def vb (q n : Nat) : Ctxt.Var (Γ₀ q n) (.polyC q n) := .there .here

/-- The output context after the four bindings `ta, tb, p, c`. -/
abbrev Δout (q n : Nat) : Ctxt polyDialect :=
  .polyC q n :: .polyN q n :: .polyN q n :: .polyN q n :: Γ₀ q n

/-- The relationally-compiled `nttMul` fragment, authored entirely through the
    engine's `bindOp` fragment builders. Each `bindOp` binds one `PolyOp` and
    threads the De Bruijn context.

    * `ta = ntt a`  binds at idx 0; afterwards `a,b` shift to `1,2`.
    * `tb = ntt b`  reads `b` at shifted index (`.there (.there .here)`).
    * `p  = basemul ta tb`  reads `ta` at `there here`, `tb` at `here`.
    * `c  = intt p`  reads `p` at `here`. -/
def nttMulFrag (q n : Nat) : PFrag (Γ₀ q n) (Δout q n) :=
  fun {s} k =>
    bindOp (.ntt q n) (.cons (va q n) .nil)
      (bindOp (.ntt q n) (.cons (.there (.there .here)) .nil)
        (bindOp (.basemul q n) (.cons (.there .here) (.cons .here .nil))
          (bindOp (.intt q n) (.cons .here .nil) k)))

/-- The full program: the fragment closed with `ret` of the coefficient-form
    result (idx 0). -/
noncomputable def nttMulProg (q n : Nat) : Com polyDialect (Γ₀ q n) (.polyC q n) :=
  nttMulFrag q n (Com.ret .here)

/-- The composite poly-ring state-step the kernel refines, assembled from the
    four atomic `pOpStep`s. -/
noncomputable def nttMulStep (q n : Nat) : PStateStep (Γ₀ q n) (Δout q n) :=
  fun V =>
    pOpStep (.intt q n) (.cons .here .nil)
      (pOpStep (.basemul q n) (.cons (.there .here) (.cons .here .nil))
        (pOpStep (.ntt q n) (.cons (.there (.there .here)) .nil)
          (pOpStep (.ntt q n) (.cons (va q n) .nil) V)))

/-- **The kernel refines its assembled state-step** — proved purely by composing
    `PRefines.polyOp` with `PRefines.seq` (no `Com.denote` blast). This is the
    Poly-dialect "rupicola" assembly: the spec is built bottom-up from the
    atomic op lemmas. -/
theorem nttMulFrag_refines (q n : Nat) :
    PRefines (nttMulStep q n) (nttMulFrag q n) :=
  PRefines.seq (PRefines.polyOp (.ntt q n) (.cons (va q n) .nil))
    (PRefines.seq
      (PRefines.polyOp (.ntt q n) (.cons (.there (.there .here)) .nil))
      (PRefines.seq
        (PRefines.polyOp (.basemul q n) (.cons (.there .here) (.cons .here .nil)))
        (PRefines.polyOp (.intt q n) (.cons .here .nil))))

/-- **Closed-form denotation lemma.** On coefficient-form inputs `a, b`, the
    relationally-compiled program denotes exactly the NTT round-trip
    `intt (basemul (ntt a) (ntt b))` — i.e. the negacyclic ring product
    `realNttMul` (CompPoly's `fastMulImpl`), the value the dialect's
    `nttMul_negacyclic_coeff` ties to the explicit negacyclic convolution. This
    is the deep tie: authoring the rewrite through the engine yields exactly the
    abstract polynomial-ring multiply.

    NOTE: `polyDenote` is `noncomputable`, so this is verified by denote-equality
    at the dialect, NOT by `#eval` (a poly-level `#eval` would also risk the
    shared LSP — the butterfly `#eval` below is the small confirmable check). -/
theorem nttMulProg_denote [Fact (Nat.Prime q)]
    (a b : CPolynomial (ZMod q)) :
    (nttMulProg q n).denote
        ((.cons a (.cons b .nil)) : Ctxt.Valuation (Γ₀ q n))
      = inttF (ND.dom q)
          (basemulF (ND.dom q) (nttF (ND.dom q) a) (nttF (ND.dom q) b)) := by
  show (if h : Nat.Prime q then
          (haveI : Fact (Nat.Prime q) := ⟨h⟩
           inttF (ND.dom q)
             (if h₂ : Nat.Prime q then
                (haveI : Fact (Nat.Prime q) := ⟨h₂⟩
                 basemulF (ND.dom q)
                   (if h₃ : Nat.Prime q then
                      (haveI : Fact (Nat.Prime q) := ⟨h₃⟩; nttF (ND.dom q) a)
                    else (#[] : Array (ZMod q)))
                   (if h₄ : Nat.Prime q then
                      (haveI : Fact (Nat.Prime q) := ⟨h₄⟩; nttF (ND.dom q) b)
                    else (#[] : Array (ZMod q))))
              else (#[] : Array (ZMod q))))
        else (0 : CPolynomial (ZMod q)))
      = _
  rw [dif_pos (Fact.out : Nat.Prime q), dif_pos (Fact.out : Nat.Prime q),
      dif_pos (Fact.out : Nat.Prime q), dif_pos (Fact.out : Nat.Prime q)]

end NttMulDemo

/-! ## 6. Demonstration B: one Cooley–Tukey butterfly, authored via the FIELD
       engine, with a small `#eval`-safe check

The radix-2 NTT butterfly `(a, b) ↦ (a + ζ·b, a − ζ·b)` over `ZMod q` is the
*scalar leaf* of every NTT layer (`PolyLowering.ctButterfly`). It is below the
polynomial-ring ops — it is plain field arithmetic — so it is authored through
the `FieldDialect` engine (`RelationalCompileHigh.bindOp`/`seq`), reusing the
shared dialect-polymorphic substrate at `fieldDialect`.

We author the *forward butterfly's two outputs* as two field programs over the
ML-KEM modulus `q = 3329`:

    s = a + ζ·b        (the "sum" output)        spec = (ctButterfly ζ a b).1
    d = a − ζ·b        (the "difference" output) spec = (ctButterfly ζ a b).2

Input context `[fp q, fp q, fp q]` holding `ζ, a, b` at indices `0, 1, 2`. -/

namespace ButterflyDemo

open CatCrypt.Crypto.SecureCompilation.RelationalCompileHigh
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.Optimizer.Lattice.NTTButterflyPass (ctButterfly)

variable {q : Nat}

/-- The butterfly input context: twiddle `ζ` and the pair `a, b`. -/
abbrev Γbf (q : Nat) : Ctxt fieldDialect := [.fp q, .fp q, .fp q]

/-- De Bruijn variables `ζ, a, b` at indices `0, 1, 2`. -/
def vζ (q : Nat) : Ctxt.Var (Γbf q) (.fp q) := .here
def va (q : Nat) : Ctxt.Var (Γbf q) (.fp q) := .there .here
def vb (q : Nat) : Ctxt.Var (Γbf q) (.fp q) := .there (.there .here)

/-- The "sum" output `s = a + ζ·b`, authored via the field engine:

        let t = fMul ζ b        -- t = ζ·b at idx 0; ζ,a,b shift to 1,2,3
        let s = fAdd a t        -- a at idx 2, t at idx 0
        ret s -/
def sumProg (q : Nat) : Com fieldDialect (Γbf q) (.fp q) :=
  RelationalCompileHigh.bindOp (.fMul q) (.cons (vζ q) (.cons (vb q) .nil))
    (RelationalCompileHigh.bindOp (.fAdd q)
      (.cons (.there (.there .here)) (.cons .here .nil))
      (Com.ret .here))

/-- The "difference" output `d = a − ζ·b`, authored via the field engine:

        let t = fMul ζ b        -- t = ζ·b at idx 0
        let d = fSub a t        -- a at idx 2, t at idx 0
        ret d -/
def diffProg (q : Nat) : Com fieldDialect (Γbf q) (.fp q) :=
  RelationalCompileHigh.bindOp (.fMul q) (.cons (vζ q) (.cons (vb q) .nil))
    (RelationalCompileHigh.bindOp (.fSub q)
      (.cons (.there (.there .here)) (.cons .here .nil))
      (Com.ret .here))

/-- **The sum output denotes to the butterfly's first coordinate.** On a twiddle
    `ζ` and inputs `a, b`, the field-engine-authored program denotes exactly to
    `(ctButterfly ζ a b).1 = a + ζ·b`. -/
theorem sumProg_denote (q : Nat) (ζ a b : ZMod q) :
    (sumProg q).denote (.cons ζ (.cons a (.cons b .nil)))
      = (ctButterfly ζ a b).1 := by
  rfl

/-- **The difference output denotes to the butterfly's second coordinate** —
    `(ctButterfly ζ a b).2 = a − ζ·b`. -/
theorem diffProg_denote (q : Nat) (ζ a b : ZMod q) :
    (diffProg q).denote (.cons ζ (.cons a (.cons b .nil)))
      = (ctButterfly ζ a b).2 := by
  rfl

/-- **Both outputs together reconstruct the full Cooley–Tukey butterfly.** The
    pair of the two field-engine programs is exactly `ctButterfly ζ a b`. -/
theorem butterfly_denote (q : Nat) (ζ a b : ZMod q) :
    ((sumProg q).denote (.cons ζ (.cons a (.cons b .nil))),
     (diffProg q).denote (.cons ζ (.cons a (.cons b .nil))))
      = ctButterfly ζ a b := by
  rfl

end ButterflyDemo

/-! ## 7. Tiny `#eval`-safe smoke check (single residue mod q = 3329)

ML-KEM modulus `q = 3329`. Take twiddle `ζ = 17` (the first ML-KEM forward
twiddle, `MlkemNttLayout`'s root), inputs `a = 100`, `b = 5`. Then

    s = a + ζ·b = 100 + 17·5 = 100 + 85 = 185   (mod 3329)
    d = a − ζ·b = 100 − 85 = 15                 (mod 3329)

Both are single `ZMod 3329` modular operations — safe to evaluate (this does NOT
blow up the shared LSP the way a full bignum/NTT array kernel would). -/

/-- Sum-output sanity: `100 + 17·5 = 185 (mod 3329)`. A single residue. -/
example :
    (ButterflyDemo.sumProg 3329).denote
        (.cons (17 : ZMod 3329) (.cons (100 : ZMod 3329) (.cons (5 : ZMod 3329) .nil)))
      = (185 : ZMod 3329) := by
  rfl

/-- Difference-output sanity: `100 − 17·5 = 15 (mod 3329)`. A single residue. -/
example :
    (ButterflyDemo.diffProg 3329).denote
        (.cons (17 : ZMod 3329) (.cons (100 : ZMod 3329) (.cons (5 : ZMod 3329) .nil)))
      = (15 : ZMod 3329) := by
  rfl

-- Tiny single-element `#eval` confirming the engine-authored butterfly's sum
-- output `a + ζ·b` computes the residue `185` mod `3329` (prints `185`).
#eval ((ButterflyDemo.sumProg 3329).denote
        (.cons (17 : ZMod 3329) (.cons (100 : ZMod 3329) (.cons (5 : ZMod 3329) .nil)))).val

-- Tiny single-element `#eval` confirming the difference output `a − ζ·b`
-- computes the residue `15` mod `3329` (prints `15`).
#eval ((ButterflyDemo.diffProg 3329).denote
        (.cons (17 : ZMod 3329) (.cons (100 : ZMod 3329) (.cons (5 : ZMod 3329) .nil)))).val

end CatCrypt.Crypto.SecureCompilation.PolyRelationalCompileHigh
