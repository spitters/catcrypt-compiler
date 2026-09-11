/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.RupicolaField
public import CatCrypt.Crypto.SecureCompilation.RupicolaField

/-!
# `RupicolaFieldExt`: full-kernel combinators for the shift-free authoring layer

`RupicolaField.lean` gives the index-free authoring combinators (`mul`/`add`/
`sub`/`neg`, `FRef`/`FBuilder`) over the high `fieldDialect`, and demonstrates
them on a flat 4- and 8-input dot product. This module closes its three honest
gaps to authoring a **full** kernel:

1. **Missing op combinators.** `RupicolaField` only exposes the four prime-field
   binops/unop. A real kernel needs `inv` (prime-field inverse) and the
   extension-tower ops (`ext2mul`/`ext2add`/`ext2sub`/`frob2`/`ext6mul`/
   `ext12mul`/…). Each is a one-line `FBuilder.bindStep` wrapper — added in §1.

2. **Deep back-references still cost manual `FRef.shift`s.** In `Demo4`, the
   accumulation loop reads inputs and the running accumulator through a
   hand-counted stack of `FRef.shift`s (five deep for the last term). §2 adds the
   do-style binder `letBind` (the imperative `bindStep`-then-continue spelling,
   shift-free for the freshest binding) and `retHead`; §3 then adds the
   base-portable builder `GBuilder`, which resolves **kernel inputs** through a
   stored weakening hom (`resolve`) and supplies the **running accumulator** from
   the live builder (`head`), so a straight-line kernel's inputs and accumulator
   are read at any depth with no `.there` and no `FRef.shift`.

3. **`toProg` needs a `b.Δ = s :: tail` witness.** §2 adds `retHead` (and §3's
   `GBuilder.ret`), which closes a builder by returning its last binding with the
   witness discharged internally (`rfl`), so the author writes neither the
   witness nor `Com.ret`.

## The real-kernel demonstration (§4)

We re-author a genuine kernel slice — the **Poseidon2 `x⁷` S-box fused with one
MDS-matrix row** over `ZMod p` — over `GBuilder`, using *only* the combinators:
no hand `bindOp`, no `.there`. The S-box `x² = s·s; x³ = x²·s; x⁶ = (x³)²;
x⁷ = x⁶·s` is a 4-deep multiply chain whose input `s` recurs at De Bruijn depth
up to 4 by hand — read shift-free here. Fused with the 4-wide MDS row
`s⁷·m₀ + s₁·m₁ + s₂·m₂ + s₃·m₃` it is an 11-binding straight-line program; the
products are shift-free, and each running sum reads the prior sum via the single
*checked-depth* helper `head1` (depth `1`, by `rfl`, not a hand `.there`). We
read its assembled `FRefines` proof straight off the builder and confirm a single
`ZMod 7` residue by `rfl`. The one residual — a fully rehoming handle on
intermediate *results* — is named in §3.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.RelationalCompileHigh

/- The extension combinators are added to the **`RupicolaField` namespace** (the
home of `FBuilder`), so they are reachable by dot notation (`b.inv`, `b.ext2mul`,
`b.letBind`, …) exactly like the core `mul`/`add`. The file is a new, additive
module that only imports `RupicolaField`. -/
namespace CatCrypt.Crypto.SecureCompilation.RupicolaField

/-! ## 1. The missing op combinators (one-line `bindStep` wrappers)

Each combinator mirrors `FBuilder.mul`/`add`/…: it takes its operands as
portable `FRef`s valid in the builder's current output context `b.Δ`, resolves
them with `FRef.now`, and appends one `bindStep`. No author ever writes `.there`. -/

/-- `b.inv x`: bind `x⁻¹ : fp p` (prime-field inverse). -/
def FBuilder.inv {Γ : Ctxt fieldDialect} {p : Nat} (b : FBuilder Γ)
    (x : FRef b.Δ (FieldTy.fp p)) : FBuilder Γ :=
  b.bindStep (.fInv p) (.cons x.now .nil)

/-- `b.ext2mul x y`: bind the `Fp2` Karatsuba product `x * y : fp2 p`. -/
def FBuilder.ext2mul {Γ : Ctxt fieldDialect} {p : Nat} (b : FBuilder Γ)
    (x y : FRef b.Δ (FieldTy.fp2 p)) : FBuilder Γ :=
  b.bindStep (.ext2Mul p) (.cons x.now (.cons y.now .nil))

/-- `b.ext2add x y`: bind the `Fp2` componentwise sum `x + y : fp2 p`. -/
def FBuilder.ext2add {Γ : Ctxt fieldDialect} {p : Nat} (b : FBuilder Γ)
    (x y : FRef b.Δ (FieldTy.fp2 p)) : FBuilder Γ :=
  b.bindStep (.ext2Add p) (.cons x.now (.cons y.now .nil))

/-- `b.ext2sub x y`: bind the `Fp2` componentwise difference `x - y : fp2 p`. -/
def FBuilder.ext2sub {Γ : Ctxt fieldDialect} {p : Nat} (b : FBuilder Γ)
    (x y : FRef b.Δ (FieldTy.fp2 p)) : FBuilder Γ :=
  b.bindStep (.ext2Sub p) (.cons x.now (.cons y.now .nil))

/-- `b.frob2 x`: bind the `Fp2` Frobenius (conjugation) `x^p : fp2 p`. -/
def FBuilder.frob2 {Γ : Ctxt fieldDialect} {p : Nat} (b : FBuilder Γ)
    (x : FRef b.Δ (FieldTy.fp2 p)) : FBuilder Γ :=
  b.bindStep (.frobenius2 p) (.cons x.now .nil)

/-- `b.ext6mul ξ₀ x y`: bind the `Fp6` product `x * y : fp6 p` (non-residue `ξ₀`). -/
def FBuilder.ext6mul {Γ : Ctxt fieldDialect} {p : Nat} (b : FBuilder Γ)
    (ξ0 : ZMod p) (x y : FRef b.Δ (FieldTy.fp6 p)) : FBuilder Γ :=
  b.bindStep (.ext6Mul p ξ0) (.cons x.now (.cons y.now .nil))

/-- `b.ext6add x y`: bind the `Fp6` componentwise sum `x + y : fp6 p`. -/
def FBuilder.ext6add {Γ : Ctxt fieldDialect} {p : Nat} (b : FBuilder Γ)
    (x y : FRef b.Δ (FieldTy.fp6 p)) : FBuilder Γ :=
  b.bindStep (.ext6Add p) (.cons x.now (.cons y.now .nil))

/-- `b.ext6sub x y`: bind the `Fp6` componentwise difference `x - y : fp6 p`. -/
def FBuilder.ext6sub {Γ : Ctxt fieldDialect} {p : Nat} (b : FBuilder Γ)
    (x y : FRef b.Δ (FieldTy.fp6 p)) : FBuilder Γ :=
  b.bindStep (.ext6Sub p) (.cons x.now (.cons y.now .nil))

/-- `b.ext12mul ξ₀ x y`: bind the `Fp12` (`GT`) product `x * y : fp12 p`. -/
def FBuilder.ext12mul {Γ : Ctxt fieldDialect} {p : Nat} (b : FBuilder Γ)
    (ξ0 : ZMod p) (x y : FRef b.Δ (FieldTy.fp12 p)) : FBuilder Γ :=
  b.bindStep (.ext12Mul p ξ0) (.cons x.now (.cons y.now .nil))

/-- `b.ext12add x y`: bind the `Fp12` componentwise sum `x + y : fp12 p`. -/
def FBuilder.ext12add {Γ : Ctxt fieldDialect} {p : Nat} (b : FBuilder Γ)
    (x y : FRef b.Δ (FieldTy.fp12 p)) : FBuilder Γ :=
  b.bindStep (.ext12Add p) (.cons x.now (.cons y.now .nil))

/-- `b.ext12sub x y`: bind the `Fp12` componentwise difference `x - y : fp12 p`. -/
def FBuilder.ext12sub {Γ : Ctxt fieldDialect} {p : Nat} (b : FBuilder Γ)
    (x y : FRef b.Δ (FieldTy.fp12 p)) : FBuilder Γ :=
  b.bindStep (.ext12Sub p) (.cons x.now (.cons y.now .nil))

/-! ## 2. The do-style binder (`letBind`) and the `retHead` closer

### `retHead`: close a builder with no witness

`FBuilder.toProg` asks the author for a proof `b.Δ = s :: b.Δ.tail`. After any
`bindStep` the output context is *definitionally* `ret op :: b.Δ`, so the witness
is `rfl` — but it is still boilerplate. `retHead` packages a builder whose head
binding is `s` together with the `Com` it closes to, discharging the witness
internally.

### `letBind`: fully index-free accumulation

The shift-counting in `Demo4` comes from one fact: `FRef.head` is portable only
from the builder's *current* output context, so as the context grows the author
re-weakens it by hand (`FRef.shift (FRef.shift …)`).

`letBind` removes that. It binds one op, then hands the continuation the fresh
value as a reference that is portable from `b.Δ` **before** the bind. Because an
`FRef` weakens itself to *any* extension, when the continuation later reaches a
larger context the same handle resolves there with no manual shifting — the
continuation just writes the handle's name. -/

/-- Close a builder whose last binding has type `s` by returning that value.
    The `b.Δ = s :: b.Δ.tail` witness `toProg` needs is discharged internally
    (`rfl`), so the author writes neither it nor `Com.ret`. Apply after any
    combinator (`mul`, `ext2mul`, …) whose result type is `s`. -/
def FBuilder.retHead {Γ : Ctxt fieldDialect} {s : FieldTy}
    (b : FBuilder Γ) (h : b.Δ = s :: b.Δ.tail := by rfl) :
    Com fieldDialect Γ s :=
  b.toProg h

/-- The do-style let-binder. Bind op `op` with arguments `args` (resolved
    `Var b.Δ`s), then run the continuation `k` on the resulting builder, handing
    it the freshly-bound value as `FRef.head` and the post-bind builder. The
    continuation names the fresh value directly (no index) for the *immediate*
    next op — the common straight-line case reads top-to-bottom like imperative
    code, with `letBind` the imperative spelling of `bindStep`-then-continue.

    `letBind` returns whatever the continuation returns (a closed `Com`).

    **Scope.** The handle `letBind` delivers is portable from the *post-bind*
    context, so it is shift-free only while it stays the freshest binding. If the
    continuation binds further ops and then reads this value again, the value is
    no longer at index `0` and the author must weaken it — `letBind` alone does
    not auto-rehome a captured result past later binds. The base-portable
    `GBuilder` (§3) closes this for inputs and the running accumulator; a fully
    rehoming *result* handle is the named residual (see §3's note). -/
def FBuilder.letBind {Γ : Ctxt fieldDialect} {s : FieldTy} (b : FBuilder Γ)
    (op : FieldOp)
    (args : HVector (fun ty => Ctxt.Var b.Δ ty)
              (DialectSignature.sig (d := fieldDialect) op))
    (k : (b' : FBuilder Γ) →
         FRef b'.Δ (DialectSignature.ret (d := fieldDialect) op) →
         Com fieldDialect Γ s) :
    Com fieldDialect Γ s :=
  let b' := b.bindStep op args
  k b' FRef.head

/-! ## 3. The base-portable builder `GBuilder` — fully index-free accumulation

The residual shift in §2 is structural: a fresh `FRef.head` is portable only from
its *bind-point* context, so when an input is read after intervening binds the
author still re-weakens it. `GBuilder` removes that for the two operand classes a
straight-line kernel actually uses:

* **kernel inputs** are resolved through a stored weakening `hom : Γ₀ → Δ` from
  the fixed input context `Γ₀` (`GBuilder.resolve`), so an input handle works at
  *any* depth with no shift — this is what kills the `Demo4`-style input chains;
* the **running accumulator** (the most recent binding) is supplied by the
  builder itself (`GBuilder.head`), recomputed from the live context, so the
  author names it without an index.

Each binder (`mulI`/`addI`/`mulAccI`/`sqAcc`/`addAccI`/`fmaI`) extends the stored
hom by one `weakenOne` automatically. So the S-box chain and the products in an
MDS row are **fully index-free** — no `.there`, no `FRef.shift`.

### Residual (the honest gap that remains)

A *general* multi-term sum `Σ pᵢ` must read a value that is **not** the freshest
binding: forming `pᵢ = sᵢ·mᵢ` pushes the running sum one slot down, so `acc + pᵢ`
reads the sum at De Bruijn depth `1`. `GBuilder.head1` supplies that one-deep read
as a **checked-depth** witness (`g.fb.Δ = a :: s :: rest`, discharged by `rfl`) —
*not* a hand-written `.there` chain, but still a depth the author is aware of.
`fmaI` packages the `prod`-then-`add` pair so even this is one combinator call.
A *fully* shift-free general accumulator would require base-portable handles on
**intermediate results** (not just inputs): each result ref would carry its home
context plus an on-resolve weakening to the builder's current `Δ`. That is the
one capability `letBind` (§2) cannot yet deliver — see its note — and the natural
next extension of this layer (a `GRef` result handle re-homing through the stored
hom). It is not needed for any kernel whose reuse is input-dominated. -/

/-- A base-portable builder: an `FBuilder` from the fixed input context `Γ₀`,
    paired with the accumulated weakening `hom : Γ₀ → Δ` so that any input
    `FRef Γ₀ t` resolves to a `Var Δ t` at the current depth with no manual
    shifting. -/
structure GBuilder (Γ₀ : Ctxt fieldDialect) where
  /-- The underlying proof-carrying builder. -/
  fb : FBuilder Γ₀
  /-- The accumulated weakening from the fixed input context to the current
      output context — generated by the binders, never by the author. -/
  hom : Ctxt.Hom Γ₀ fb.Δ

/-- Start a base-portable build: the empty builder with the identity weakening. -/
def GBuilder.start (Γ₀ : Ctxt fieldDialect) : GBuilder Γ₀ where
  fb := FBuilder.start Γ₀
  hom := Ctxt.Hom.id Γ₀

/-- Resolve a kernel **input** `FRef Γ₀ t` to a concrete `Var g.fb.Δ t` at the
    current depth — through the stored hom, so the same input handle works at any
    point in the kernel with no shift. -/
def GBuilder.resolve {Γ₀ : Ctxt fieldDialect} {t : FieldTy} (g : GBuilder Γ₀)
    (r : FRef Γ₀ t) : Ctxt.Var g.fb.Δ t :=
  r g.hom

/-- The handle on the **most-recently bound** value, valid at the current depth.
    Returned by every binder so the author names the fresh value without an index. -/
def GBuilder.head {Γ₀ : Ctxt fieldDialect} (g : GBuilder Γ₀) {s : FieldTy}
    (h : g.fb.Δ = s :: g.fb.Δ.tail := by rfl) : Ctxt.Var g.fb.Δ s :=
  h ▸ Ctxt.Var.here

/-- Append one op (arguments as resolved `Var g.fb.Δ`s) to a base-portable
    builder, extending the stored hom by one weakening automatically. -/
def GBuilder.bindStep {Γ₀ : Ctxt fieldDialect} (g : GBuilder Γ₀) (op : FieldOp)
    (args : HVector (fun ty => Ctxt.Var g.fb.Δ ty)
              (DialectSignature.sig (d := fieldDialect) op)) :
    GBuilder Γ₀ where
  fb := g.fb.bindStep op args
  hom := (Ctxt.Hom.weakenOne g.fb.Δ
            (DialectSignature.ret (d := fieldDialect) op)).comp g.hom

/-- Multiply two **inputs** (resolved through the stored hom). -/
def GBuilder.mulI {Γ₀ : Ctxt fieldDialect} {p : Nat} (g : GBuilder Γ₀)
    (x y : FRef Γ₀ (FieldTy.fp p)) : GBuilder Γ₀ :=
  g.bindStep (.fMul p) (.cons (g.resolve x) (.cons (g.resolve y) .nil))

/-- Add two **inputs** (resolved through the stored hom). -/
def GBuilder.addI {Γ₀ : Ctxt fieldDialect} {p : Nat} (g : GBuilder Γ₀)
    (x y : FRef Γ₀ (FieldTy.fp p)) : GBuilder Γ₀ :=
  g.bindStep (.fAdd p) (.cons (g.resolve x) (.cons (g.resolve y) .nil))

/-- Multiply an **input** by the current **accumulator** (= last binding). The
    accumulator is supplied by the builder (`g.head`), so neither operand needs a
    shift. -/
def GBuilder.mulAccI {Γ₀ : Ctxt fieldDialect} {p : Nat} (g : GBuilder Γ₀)
    (x : FRef Γ₀ (FieldTy.fp p))
    (hAcc : g.fb.Δ = FieldTy.fp p :: g.fb.Δ.tail := by rfl) : GBuilder Γ₀ :=
  g.bindStep (.fMul p) (.cons (g.head hAcc) (.cons (g.resolve x) .nil))

/-- Square the current **accumulator** (= last binding). -/
def GBuilder.sqAcc {Γ₀ : Ctxt fieldDialect} {p : Nat} (g : GBuilder Γ₀)
    (hAcc : g.fb.Δ = FieldTy.fp p :: g.fb.Δ.tail := by rfl) : GBuilder Γ₀ :=
  g.bindStep (.fMul p) (.cons (g.head hAcc) (.cons (g.head hAcc) .nil))

/-- Add an **input** to the current **accumulator** (= last binding). -/
def GBuilder.addAccI {Γ₀ : Ctxt fieldDialect} {p : Nat} (g : GBuilder Γ₀)
    (x : FRef Γ₀ (FieldTy.fp p))
    (hAcc : g.fb.Δ = FieldTy.fp p :: g.fb.Δ.tail := by rfl) : GBuilder Γ₀ :=
  g.bindStep (.fAdd p) (.cons (g.head hAcc) (.cons (g.resolve x) .nil))

/-- The value bound **one before** the most recent (De Bruijn index `1`), valid
    at the current depth. The depth is a *checked* witness (`rfl`), not a hand-
    written `.there` chain: the author supplies `a, rest` such that the current
    context is `a :: s :: rest` and Lean computes the `.there .here` index. This
    is the single helper a faithful multi-term accumulation needs — to add a
    freshly-formed product to the *previous* running sum (which the product's
    bind pushed one slot down). -/
def GBuilder.head1 {Γ₀ : Ctxt fieldDialect} (g : GBuilder Γ₀)
    {a s : FieldTy} {rest : Ctxt fieldDialect}
    (h : g.fb.Δ = a :: s :: rest := by rfl) :
    Ctxt.Var g.fb.Δ s :=
  h ▸ Ctxt.Var.there Ctxt.Var.here

/-- Form the product `x·y` of two **inputs** and add it to the **previous**
    running sum (the accumulator before this product was bound). This is the
    faithful MDS-row accumulation step `acc ← acc + x·y`, realized as
    `prod = x·y` (pushes `acc` one slot down) then `acc + prod`, reading the old
    accumulator with the *checked-depth* `head1` (no `.there`). -/
def GBuilder.fmaI {Γ₀ : Ctxt fieldDialect} {p : Nat} (g : GBuilder Γ₀)
    (x y : FRef Γ₀ (FieldTy.fp p))
    (hAcc : g.fb.Δ = FieldTy.fp p :: g.fb.Δ.tail := by rfl) : GBuilder Γ₀ :=
  let gp := g.bindStep (.fMul p) (.cons (g.resolve x) (.cons (g.resolve y) .nil))
  -- now: gp.fb.Δ = (x·y) :: acc :: …; read acc via head1, prod via head
  gp.bindStep (.fAdd p)
    (.cons gp.head
      (.cons (gp.head1 (a := FieldTy.fp p) (s := FieldTy.fp p)
                (rest := g.fb.Δ.tail)
                (by show FieldTy.fp p :: g.fb.Δ = _; rw [hAcc]; rfl)) .nil))

/-- Close a base-portable builder by returning its last binding. -/
def GBuilder.ret {Γ₀ : Ctxt fieldDialect} {s : FieldTy} (g : GBuilder Γ₀)
    (h : g.fb.Δ = s :: g.fb.Δ.tail := by rfl) :
    Com fieldDialect Γ₀ s :=
  g.fb.toProg h

/-- The assembled `FRefines` proof, read straight off the underlying builder. -/
def GBuilder.refines {Γ₀ : Ctxt fieldDialect} (g : GBuilder Γ₀) :
    FRefines g.fb.spec g.fb.frag :=
  g.fb.refines

/-! ## 4. Real-kernel demonstration — Poseidon2 `x⁷` S-box ∘ one MDS row

The kernel: take a state element `s` and four MDS coefficients/state values, apply
the Poseidon2 S-box `y = s⁷`, then accumulate the MDS row
`out = y·m₀ + s₁·m₁ + s₂·m₂ + s₃·m₃` (the coefficients passed as field inputs,
since the dialect's ops range over variables — a faithful fused S-box+MDS slice).

Input context `Γ₀ = [s, m₀, s₁, m₁, s₂, m₂, s₃, m₃]` (8 prime-field inputs).

The whole kernel is authored over `GBuilder`. The S-box chain
`x² = s·s; x³ = x²·s; x⁶ = (x³)²; x⁷ = x⁶·s` is **fully index-free** — every step
reads the accumulator (`mulAccI`/`sqAcc`, supplied by the builder) and the input
`s` (resolved through the stored hom), and the input `s` is reused four times at
growing depth **with no `FRef.shift` and no `.there`**. By hand, the final `x⁷`
bind reads `s` at De Bruijn depth 4 (`.there^4 .here`) — exactly the chain the
builder removes.

The MDS accumulation `out = (((y·m₀) + s₁·m₁) + s₂·m₂) + s₃·m₃` is written
left-nested so each running sum reads the freshest accumulator; the products on
the right are formed by `mulAccI` *into* the accumulator immediately before the
add, keeping every operand either an input (hom-resolved) or the accumulator
(builder-supplied). See the residual note below for why a *general* multi-term
sum still needs one `headAt`-depth read. -/

namespace Poseidon2SBoxMDS

variable {p : Nat}

/-- The 8 prime-field inputs `s, m₀, s₁, m₁, s₂, m₂, s₃, m₃`. -/
abbrev Γ₀ (p : Nat) : Ctxt fieldDialect :=
  [FieldTy.fp p, FieldTy.fp p, FieldTy.fp p, FieldTy.fp p,
   FieldTy.fp p, FieldTy.fp p, FieldTy.fp p, FieldTy.fp p]

def s  : FRef (Γ₀ p) (FieldTy.fp p) := FRef.ofVar .here
def m0 : FRef (Γ₀ p) (FieldTy.fp p) := FRef.ofVar (.there .here)
def s1 : FRef (Γ₀ p) (FieldTy.fp p) := FRef.ofVar (.there (.there .here))
def m1 : FRef (Γ₀ p) (FieldTy.fp p) := FRef.ofVar (.there (.there (.there .here)))
def s2 : FRef (Γ₀ p) (FieldTy.fp p) :=
  FRef.ofVar (.there (.there (.there (.there .here))))
def m2 : FRef (Γ₀ p) (FieldTy.fp p) :=
  FRef.ofVar (.there (.there (.there (.there (.there .here)))))
def s3 : FRef (Γ₀ p) (FieldTy.fp p) :=
  FRef.ofVar (.there (.there (.there (.there (.there (.there .here))))))
def m3 : FRef (Γ₀ p) (FieldTy.fp p) :=
  FRef.ofVar (.there (.there (.there (.there (.there (.there (.there .here)))))))

/-- The Poseidon2 `x⁷` S-box on `s`, fully index-free.

    `x² = s·s` (`mulI s s`); then accumulator-relative:
    `x³ = x²·s` (`mulAccI s`), `x⁶ = (x³)²` (`sqAcc`), `x⁷ = x⁶·s` (`mulAccI s`).
    The input `s` reappears at growing De Bruijn depth (1,3,4 by hand) but is
    resolved through the stored hom every time — no shift. -/
def sboxBuilder (p : Nat) : GBuilder (Γ₀ p) :=
  let g0 := (GBuilder.start (Γ₀ p)).mulI s s   -- x² = s·s
  let g1 := g0.mulAccI s                         -- x³ = x²·s
  let g2 := g1.sqAcc                              -- x⁶ = (x³)²
  g2.mulAccI s                                    -- x⁷ = x⁶·s

/-- The fused S-box ∘ MDS-row kernel, authored entirely over `GBuilder`.

    Continues from the S-box accumulator `y = s⁷`:
    `acc = y·m₀` (`mulAccI m₀`), then the faithful MDS sum
    `acc ← acc + s₁·m₁`, `+ s₂·m₂`, `+ s₃·m₃` — each a single `fmaI` step
    (`prod = sᵢ·mᵢ`; `acc + prod`, the old accumulator read by the checked-depth
    `head1`, no `.there`). -/
def kernelBuilder (p : Nat) : GBuilder (Γ₀ p) :=
  let g := sboxBuilder p
  let g := g.mulAccI m0          -- acc = y·m₀
  let g := g.fmaI s1 m1          -- acc = (y·m₀) + s₁·m₁
  let g := g.fmaI s2 m2          -- acc = …      + s₂·m₂
  g.fmaI s3 m3                   -- acc = …      + s₃·m₃

/-- The closed kernel program. -/
def kernelProg (p : Nat) : Com fieldDialect (Γ₀ p) (FieldTy.fp p) :=
  (kernelBuilder p).ret

/-- **The kernel refines its auto-synthesized state-step**, read straight off the
    builder. The spec was assembled by the combinators (`FRefines.seq` /
    `FRefines.fieldOp`); the author supplied no spec, no `.there`, no shift. -/
theorem kernelProg_refines (p : Nat) :
    FRefines (kernelBuilder p).fb.spec (kernelBuilder p).fb.frag :=
  (kernelBuilder p).refines

end Poseidon2SBoxMDS

/-! ## 5. Tiny `#eval`-style smoke check (single `ZMod 7` residue, LSP-safe)

The faithful kernel `out = s⁷·m₀ + s₁·m₁ + s₂·m₂ + s₃·m₃` on
`s = 3, m₀ = 2, s₁ = m₁ = s₂ = m₂ = s₃ = m₃ = 1`:

`s⁷ = 3⁷ = 2187 ≡ 3 (mod 7)`; `y·m₀ = 3·2 = 6`; `+1·1 +1·1 +1·1 = 9 ≡ 2 (mod 7)`. -/

example :
    (Poseidon2SBoxMDS.kernelProg 7).denote
        (.cons (3 : ZMod 7) (.cons (2 : ZMod 7) (.cons (1 : ZMod 7)
          (.cons (1 : ZMod 7) (.cons (1 : ZMod 7) (.cons (1 : ZMod 7)
            (.cons (1 : ZMod 7) (.cons (1 : ZMod 7) .nil))))))))
      = (2 : ZMod 7) := by
  rfl

end CatCrypt.Crypto.SecureCompilation.RupicolaField
