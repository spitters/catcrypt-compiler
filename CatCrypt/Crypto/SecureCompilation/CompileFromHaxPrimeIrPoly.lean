/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.PolyDialect
public import HaxLean.AST

/-!
# Front recognizer: `primeir-hax` `PolyRing` trait methods → `polyDialect` ops

The `primeir-hax` crate (`primeir-hax/src/poly.rs`) exposes a `PolyRing` trait
whose method names align with the `PolyOp` operations of `polyDialect`
(`VIR/PolyDialect.lean`), with coefficient form (`Self`) and NTT form
(`PolyRing::NttForm`) as distinct Rust types. This module keys recognition on
those method names, emits each recognized op as a single-op `Com polyDialect`
leaf, and ties the leaf to the dialect's own denotation.

## Recognition table

| method      | `PolyOp` (at `q`, `n`)  | type                    | denotes to                  |
|-------------|-------------------------|-------------------------|-----------------------------|
| `ntt`       | `PolyOp.ntt q n`        | `polyC → polyN`         | `realNtt (dom q) p`         |
| `intt`      | `PolyOp.intt q n`       | `polyN → polyC`         | `inttF (dom q) a`           |
| `basemul`   | `PolyOp.basemul q n`    | `polyN → polyN → polyN` | `realBasemul (dom q) a b`   |
| `poly_add`  | `PolyOp.polyAdd q n`    | `polyC → polyC → polyC` | `p + r`                     |
| `poly_sub`  | `PolyOp.polySub q n`    | `polyC → polyC → polyC` | `p - r`                     |
| `poly_smul` | `PolyOp.polySMul q n c` | `polyC → polyC`         | `C c * p`                   |
| `ntt_mul`   | `PolyOp.nttMul q n`     | `polyC → polyC → polyC` | `realNttMul (dom q) p r`    |

The modulus `q`, the degree `n` and the scalar `c` of `poly_smul` are not
present in the trait extraction (the trait is generic over the ring, and
`haxpipeT` erases the scalar argument's value into an ordinary argument node);
they are supplied by the recognition context, as `CompileFromHaxPrimeIrField`
supplies the modulus `p` for the `Field` family.

## `ntt_add`

The trait's `ntt_add` (AddNTT, FIPS 204 Algorithm 44) has no `PolyOp`:
`polyDialect` carries no NTT-form addition. It is expressed here as the
four-op composite `ntt ∘ polyAdd ∘ (intt × intt)` (`nttAddCom`), whose
denotation is `realNtt (dom q) (inttF (dom q) a + inttF (dom q) b)`. The
entrywise form — that this equals the entrywise sum of the two evaluation
arrays — needs linearity of `realNtt`, which the CompPoly layer does not
state.

## Surface

`haxpipeT --emit-certified` records a trait-method call as an `ImpExpr.app`
node whose head is the bare method name; `primeirPolyHead` restores the
`PolyRing.<m>` qualifier under the primeir recognition context, as
`CompileFromHaxPrimeIrFront.primeirFieldHead` does for `Field`. The `ImpExpr`
literals of the three generic callers are pinned verbatim from the extraction.

## Main definitions

* `recognizePolyOp` — resolved `PolyRing` method name → `PolyOp`, fail-closed.
* `primeirPolyHead`, `recognizePrimeirPolyCall` — the bare-head bridge and the
  `ImpExpr` recognizer.
* `nttLeaf`, `inttLeaf`, `basemulLeaf`, `polyAddLeaf`, `polySubLeaf`,
  `polySMulLeaf`, `nttMulLeaf` — the single-op `Com polyDialect` emit leaves.
* `nttAddCom` — the composite standing for `ntt_add`.
* `polyMulDemoImpExpr`, `mlweEntryDemoImpExpr`, `nttDot2DemoImpExpr` — the
  pinned extraction literals of the three generic callers.
* `compilePolyBinCallC` — the pass from a recognized binary coefficient-form
  call to its emit leaf.

## Main results

* `primeir_poly_ntt_mul_recognized_denote` and its siblings — each emit leaf
  denotes to the dialect's polynomial-ring operation.
* `primeir_poly_ntt_mul_recognized_negacyclic` — the `ntt_mul` leaf denotes,
  after the `%ₘ (Xⁿ+1)` fold, to the negacyclic convolution.
* `nttAddCom_denote` — the `ntt_add` composite's denotation.
* `primeir_poly_ntt_mul_compiles_and_ties` — recognition, emit and value tie
  for the extracted `ntt_mul` call node.
* `polyMulDemo_call_pin`, `mlweEntryDemo_call_pin`, `nttDot2Demo_call_pin` —
  the call nodes sit inside the pinned extraction literals.
* `recognize_head_forms_agree` and its siblings — recognition agrees on the
  bare head and on the `PolyRing_<m>` head the emitter produces once the
  method is resolved to an `impl` the crate defines.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxPrimeIrPoly

open _root_.Hax (ImpExpr ImpLit)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.PolyDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeNTTSemantic (NttDomains enc)
open CompPoly.CPolynomial.NTT (Domain)
open CompPoly (CPolynomial)
open CatCrypt.Crypto.SecureCompilation.VIR.Negacyclic (negaPoly)
open Polynomial

/-! ## 1. The recognition table

Keyed on the resolved `PolyRing` trait-method name. Both the fully-qualified
Lean-backend name (`Primeir_hax.PolyRing.<m>`) and the bare class-method name
(`PolyRing.<m>`) are accepted. -/

/-- Recognize a resolved `primeir-hax` `PolyRing` trait-method name as the
    `PolyOp` at modulus `q`, degree `n` and scalar `c` (the scalar is used only
    by `poly_smul`). Returns `none` for any other head. -/
def recognizePolyOp (name : String) (q n : Nat) (c : ZMod q) : Option PolyOp :=
  if name = "Primeir_hax.PolyRing.ntt" ∨ name = "PolyRing.ntt" then some (.ntt q n)
  else if name = "Primeir_hax.PolyRing.intt" ∨ name = "PolyRing.intt" then some (.intt q n)
  else if name = "Primeir_hax.PolyRing.basemul" ∨ name = "PolyRing.basemul" then
    some (.basemul q n)
  else if name = "Primeir_hax.PolyRing.poly_add" ∨ name = "PolyRing.poly_add" then
    some (.polyAdd q n)
  else if name = "Primeir_hax.PolyRing.poly_sub" ∨ name = "PolyRing.poly_sub" then
    some (.polySub q n)
  else if name = "Primeir_hax.PolyRing.poly_smul" ∨ name = "PolyRing.poly_smul" then
    some (.polySMul q n c)
  else if name = "Primeir_hax.PolyRing.ntt_mul" ∨ name = "PolyRing.ntt_mul" then
    some (.nttMul q n)
  else none

@[simp] theorem recognizePoly_ntt (q n : Nat) (c : ZMod q) :
    recognizePolyOp "Primeir_hax.PolyRing.ntt" q n c = some (.ntt q n) := rfl
@[simp] theorem recognizePoly_intt (q n : Nat) (c : ZMod q) :
    recognizePolyOp "Primeir_hax.PolyRing.intt" q n c = some (.intt q n) := rfl
@[simp] theorem recognizePoly_basemul (q n : Nat) (c : ZMod q) :
    recognizePolyOp "Primeir_hax.PolyRing.basemul" q n c = some (.basemul q n) := rfl
@[simp] theorem recognizePoly_poly_add (q n : Nat) (c : ZMod q) :
    recognizePolyOp "Primeir_hax.PolyRing.poly_add" q n c = some (.polyAdd q n) := rfl
@[simp] theorem recognizePoly_poly_sub (q n : Nat) (c : ZMod q) :
    recognizePolyOp "Primeir_hax.PolyRing.poly_sub" q n c = some (.polySub q n) := rfl
@[simp] theorem recognizePoly_poly_smul (q n : Nat) (c : ZMod q) :
    recognizePolyOp "Primeir_hax.PolyRing.poly_smul" q n c = some (.polySMul q n c) := rfl
@[simp] theorem recognizePoly_ntt_mul (q n : Nat) (c : ZMod q) :
    recognizePolyOp "Primeir_hax.PolyRing.ntt_mul" q n c = some (.nttMul q n) := rfl

/-- `ntt_add` is not in the table: `polyDialect` has no NTT-form addition op.
    See `nttAddCom` for the composite that stands in for it. -/
theorem recognizePoly_ntt_add (q n : Nat) (c : ZMod q) :
    recognizePolyOp "Primeir_hax.PolyRing.ntt_add" q n c = none := rfl

/-- An unrecognized head is rejected. -/
theorem recognizePoly_unknown (q n : Nat) (c : ZMod q) :
    recognizePolyOp "Primeir_hax.Field.mul" q n c = none := rfl

/-! ## 2. Emit: a recognized op as a single-op `Com polyDialect` leaf

The coefficient/NTT form distinction of the trait is the `polyC`/`polyN`
distinction of the dialect's type alphabet, so each leaf's context and return
type are fixed by the op's signature. -/

/-- The `ntt` emit leaf: `polyC q n → polyN q n`. -/
def nttLeaf (q n : Nat) : Com polyDialect [PolyTy.polyC q n] (PolyTy.polyN q n) :=
  .var (.mk (.ntt q n) rfl (.cons .here .nil)) (.ret .here)

/-- The `intt` emit leaf: `polyN q n → polyC q n`. -/
def inttLeaf (q n : Nat) : Com polyDialect [PolyTy.polyN q n] (PolyTy.polyC q n) :=
  .var (.mk (.intt q n) rfl (.cons .here .nil)) (.ret .here)

/-- The `basemul` emit leaf: `polyN q n → polyN q n → polyN q n`. -/
def basemulLeaf (q n : Nat) :
    Com polyDialect [PolyTy.polyN q n, PolyTy.polyN q n] (PolyTy.polyN q n) :=
  .var (.mk (.basemul q n) rfl (.cons .here (.cons (.there .here) .nil))) (.ret .here)

/-- The `poly_add` emit leaf: `polyC q n → polyC q n → polyC q n`. -/
def polyAddLeaf (q n : Nat) :
    Com polyDialect [PolyTy.polyC q n, PolyTy.polyC q n] (PolyTy.polyC q n) :=
  .var (.mk (.polyAdd q n) rfl (.cons .here (.cons (.there .here) .nil))) (.ret .here)

/-- The `poly_sub` emit leaf: `polyC q n → polyC q n → polyC q n`. -/
def polySubLeaf (q n : Nat) :
    Com polyDialect [PolyTy.polyC q n, PolyTy.polyC q n] (PolyTy.polyC q n) :=
  .var (.mk (.polySub q n) rfl (.cons .here (.cons (.there .here) .nil))) (.ret .here)

/-- The `poly_smul` emit leaf at scalar `c`: `polyC q n → polyC q n`. -/
def polySMulLeaf (q n : Nat) (c : ZMod q) :
    Com polyDialect [PolyTy.polyC q n] (PolyTy.polyC q n) :=
  .var (.mk (.polySMul q n c) rfl (.cons .here .nil)) (.ret .here)

/-- The `ntt_mul` emit leaf: `polyC q n → polyC q n → polyC q n`. -/
def nttMulLeaf (q n : Nat) :
    Com polyDialect [PolyTy.polyC q n, PolyTy.polyC q n] (PolyTy.polyC q n) :=
  .var (.mk (.nttMul q n) rfl (.cons .here (.cons (.there .here) .nil))) (.ret .here)

/-- The `ntt_add` composite `ntt (polyAdd (intt a) (intt b))`, over
    `[polyN q n, polyN q n]`. The trait method it stands for has no `PolyOp`;
    this is the four-op program that produces its result from the ops the
    dialect does carry. -/
def nttAddCom (q n : Nat) :
    Com polyDialect [PolyTy.polyN q n, PolyTy.polyN q n] (PolyTy.polyN q n) :=
  .var (.mk (.intt q n) rfl (.cons .here .nil))
   (.var (.mk (.intt q n) rfl (.cons (.there (.there .here)) .nil))
    (.var (.mk (.polyAdd q n) rfl (.cons (.there .here) (.cons .here .nil)))
     (.var (.mk (.ntt q n) rfl (.cons .here .nil)) (.ret .here))))

/-! ## 3. The value ties

Each emit leaf denotes to the polynomial-ring operation `polyDialect` gives its
op, reusing the dialect's own denotation facts. The ops carrying a transform
(`ntt`, `intt`, `basemul`, `nttMul`) need the per-modulus NTT domain and a
prime modulus, as the dialect denotation does. -/

section Ties

variable {q n : Nat} [ND : NttDomains]

/-- The recognized `PolyRing::ntt` call ties to the forward transform
    `realNtt` on the NTT domain of `q`. -/
theorem primeir_poly_ntt_recognized_denote [Fact (Nat.Prime q)] (p : CPolynomial (ZMod q)) :
    (nttLeaf q n).denote (.cons p .nil) = realNtt (ND.dom q) p := by
  show (if h : Nat.Prime q then
          (haveI : Fact (Nat.Prime q) := ⟨h⟩; nttF (ND.dom q) p)
        else (#[] : Array (ZMod q))) = realNtt (ND.dom q) p
  rw [dif_pos (Fact.out : Nat.Prime q)]

/-- The recognized `PolyRing::intt` call ties to the inverse transform
    `inttF` on the NTT domain of `q`. -/
theorem primeir_poly_intt_recognized_denote [Fact (Nat.Prime q)] (a : Array (ZMod q)) :
    (inttLeaf q n).denote (.cons a .nil) = inttF (ND.dom q) a := by
  show (if h : Nat.Prime q then
          (haveI : Fact (Nat.Prime q) := ⟨h⟩; inttF (ND.dom q) a)
        else (0 : CPolynomial (ZMod q))) = inttF (ND.dom q) a
  rw [dif_pos (Fact.out : Nat.Prime q)]

/-- The recognized `PolyRing::basemul` call ties to the entrywise product of
    two evaluation arrays. -/
theorem primeir_poly_basemul_recognized_denote [Fact (Nat.Prime q)] (a b : Array (ZMod q)) :
    (basemulLeaf q n).denote (.cons a (.cons b .nil)) = realBasemul (ND.dom q) a b := by
  show (if h : Nat.Prime q then
          (haveI : Fact (Nat.Prime q) := ⟨h⟩; basemulF (ND.dom q) a b)
        else (#[] : Array (ZMod q))) = realBasemul (ND.dom q) a b
  rw [dif_pos (Fact.out : Nat.Prime q)]

/-- The recognized `PolyRing::poly_add` call ties to `CPolynomial` addition. -/
theorem primeir_poly_add_recognized_denote (p r : CPolynomial (ZMod q)) :
    (polyAddLeaf q n).denote (.cons p (.cons r .nil)) = p + r := rfl

/-- The recognized `PolyRing::poly_sub` call ties to `CPolynomial` subtraction. -/
theorem primeir_poly_sub_recognized_denote (p r : CPolynomial (ZMod q)) :
    (polySubLeaf q n).denote (.cons p (.cons r .nil)) = p - r := rfl

/-- The recognized `PolyRing::poly_smul` call at scalar `c` ties to
    multiplication by the constant polynomial `C c`. -/
theorem primeir_poly_smul_recognized_denote (c : ZMod q) (p : CPolynomial (ZMod q)) :
    (polySMulLeaf q n c).denote (.cons p .nil) = CompPoly.CPolynomial.C c * p := rfl

/-- The recognized `PolyRing::ntt_mul` call ties to `realNttMul`, the ring
    product of `Z_q[X]/(Xⁿ+1)` computed through the NTT round trip. -/
theorem primeir_poly_ntt_mul_recognized_denote [Fact (Nat.Prime q)]
    (p r : CPolynomial (ZMod q)) :
    (nttMulLeaf q n).denote (.cons p (.cons r .nil)) = realNttMul (ND.dom q) p r :=
  nttMul_denote (q := q) (n := n) p r

/-- **The recognized `ntt_mul` call ties to the negacyclic convolution.** On
    encoded inputs, the `%ₘ (Xⁿ+1)` fold of the `nttMulLeaf` denotation has
    `k`-th coefficient the negacyclic convolution of the two coefficient
    sequences, by the dialect's `nttMul_negacyclic_coeff`. -/
theorem primeir_poly_ntt_mul_recognized_negacyclic [Fact (Nat.Prime q)]
    (hD : 2 * n ≤ (ND.dom q).n) (hn : 0 < n)
    (a b : Fin n → BitVec 16) {k : Nat} (hk : k < n) :
    (((nttMulLeaf q n).denote (.cons (enc q n a) (.cons (enc q n b) .nil))).toPoly
        %ₘ negaPoly n).coeff k
      = (∑ ij ∈ Finset.antidiagonal k,
            (enc q n a).toPoly.coeff ij.1 * (enc q n b).toPoly.coeff ij.2)
        - (∑ ij ∈ Finset.antidiagonal (k + n),
            (enc q n a).toPoly.coeff ij.1 * (enc q n b).toPoly.coeff ij.2) :=
  nttMul_negacyclic_coeff (q := q) (n := n) hD hn a b hk

/-- The `ntt_add` composite denotes to the forward transform of the
    coefficient-form sum of the two inverse-transformed inputs. -/
theorem nttAddCom_denote [Fact (Nat.Prime q)] (a b : Array (ZMod q)) :
    (nttAddCom q n).denote (.cons a (.cons b .nil))
      = realNtt (ND.dom q) (inttF (ND.dom q) a + inttF (ND.dom q) b) := by
  show (if h : Nat.Prime q then
          (haveI : Fact (Nat.Prime q) := ⟨h⟩;
            nttF (ND.dom q)
              (polyAddF
                (if h : Nat.Prime q then
                  (haveI : Fact (Nat.Prime q) := ⟨h⟩; inttF (ND.dom q) a)
                 else (0 : CPolynomial (ZMod q)))
                (if h : Nat.Prime q then
                  (haveI : Fact (Nat.Prime q) := ⟨h⟩; inttF (ND.dom q) b)
                 else (0 : CPolynomial (ZMod q)))))
        else (#[] : Array (ZMod q)))
      = realNtt (ND.dom q) (inttF (ND.dom q) a + inttF (ND.dom q) b)
  simp only [dif_pos (Fact.out : Nat.Prime q)]

end Ties

/-! ## 4. The extraction surface, pinned

The `ImpExpr` literals below are copied verbatim from the `haxpipeT
--emit-certified --name Primeir` extraction of `primeir-hax`
(`primeir-hax/src/poly.rs` at SSProve-lean commit
`3e6e6eee6746382f3230f76d649261812e6fdfb9`). A rename in the Rust changes the
head strings and the `rfl` pins below stop holding. -/

/-- `poly_mul_demo`'s body as extracted: `ntt_mul(a, b)`. -/
def polyMulDemoImpExpr : ImpExpr :=
  (.letBind "a" (.var "a") (.letBind "b" (.var "b") (.app "ntt_mul" [(.var "a"), (.var "b")])))

/-- `mlwe_entry_demo`'s body as extracted:
    `poly_add(intt(basemul(a_hat, ntt(s))), e)`. -/
def mlweEntryDemoImpExpr : ImpExpr :=
  (.letBind "a_hat" (.var "a_hat") (.letBind "s" (.var "s") (.letBind "e" (.var "e")
    (.app "poly_add" [(.app "intt" [(.app "basemul" [(.var "a_hat"),
      (.app "ntt" [(.var "s")])])]), (.var "e")]))))

/-- `ntt_dot2_demo`'s body as extracted:
    `ntt_add(basemul(a0, v0), basemul(a1, v1))`. -/
def nttDot2DemoImpExpr : ImpExpr :=
  (.letBind "a0" (.var "a0") (.letBind "a1" (.var "a1") (.letBind "v0" (.var "v0")
    (.letBind "v1" (.var "v1") (.app "ntt_add" [(.app "basemul" [(.var "a0"), (.var "v0")]),
      (.app "basemul" [(.var "a1"), (.var "v1")])])))))

/-- `MODULUS_MLDSA` on the extraction surface: `q = 2^23 − 2^13 + 1`. -/
def mldsaModulusImpExpr : ImpExpr := .lit (ImpLit.int 8380417)

/-- The ML-DSA modulus as a `Nat`, the recognition context's `q` for an
    extraction of an ML-DSA `PolyRing` instance. -/
def mldsaModulus : Nat := 8380417

/-- The pinned literal carries the ML-DSA modulus. -/
theorem mldsaModulusImpExpr_pin :
    mldsaModulusImpExpr = .lit (ImpLit.int (Int.ofNat mldsaModulus)) := rfl

/-- The `ntt_mul` call node of `poly_mul_demo`. -/
def nttMulCall : ImpExpr := .app "ntt_mul" [.var "a", .var "b"]

/-- The `poly_add` call node of `mlwe_entry_demo`. -/
def polyAddCall : ImpExpr :=
  .app "poly_add" [(.app "intt" [(.app "basemul" [(.var "a_hat"),
    (.app "ntt" [(.var "s")])])]), (.var "e")]

/-- The `ntt_add` call node of `ntt_dot2_demo`. -/
def nttAddCall : ImpExpr :=
  .app "ntt_add" [(.app "basemul" [(.var "a0"), (.var "v0")]),
    (.app "basemul" [(.var "a1"), (.var "v1")])]

/-- The `ntt_mul` call node is the body of the pinned `poly_mul_demo`. -/
theorem polyMulDemo_call_pin :
    polyMulDemoImpExpr = .letBind "a" (.var "a") (.letBind "b" (.var "b") nttMulCall) := rfl

/-- The `poly_add` call node is the body of the pinned `mlwe_entry_demo`. -/
theorem mlweEntryDemo_call_pin :
    mlweEntryDemoImpExpr =
      .letBind "a_hat" (.var "a_hat") (.letBind "s" (.var "s")
        (.letBind "e" (.var "e") polyAddCall)) := rfl

/-- The `ntt_add` call node is the body of the pinned `ntt_dot2_demo`. -/
theorem nttDot2Demo_call_pin :
    nttDot2DemoImpExpr =
      .letBind "a0" (.var "a0") (.letBind "a1" (.var "a1")
        (.letBind "v0" (.var "v0") (.letBind "v1" (.var "v1") nttAddCall))) := rfl

/-! ## 5. Bare-head bridge and the `ImpExpr` recognizer

`haxpipeT` records the call by its bare method name, dropping the trait
qualifier; restore it under the primeir recognition context and key
`recognizePolyOp` on the result. -/

/-- Restore the `PolyRing.<m>` trait qualifier for a `PolyRing` method head.
    Both emitted forms are accepted: the bare method name, which `haxpipeT`
    produces for a method it leaves in the `Deps` class, and the
    `PolyRing_<m>` form it produces for a method resolved to an `impl` the
    crate defines. Any other head passes through unchanged, so it still fails
    `recognizePolyOp`.

    The arms are written out rather than derived by stripping a prefix because
    `String.startsWith` and `String.drop` do not reduce definitionally under
    the module system, and the recognition fixtures below are `rfl`. -/
def primeirPolyHead (f : String) : String :=
  if f = "ntt" then "PolyRing.ntt"
  else if f = "PolyRing_ntt" then "PolyRing.ntt"
  else if f = "intt" then "PolyRing.intt"
  else if f = "PolyRing_intt" then "PolyRing.intt"
  else if f = "basemul" then "PolyRing.basemul"
  else if f = "PolyRing_basemul" then "PolyRing.basemul"
  else if f = "poly_add" then "PolyRing.poly_add"
  else if f = "PolyRing_poly_add" then "PolyRing.poly_add"
  else if f = "poly_sub" then "PolyRing.poly_sub"
  else if f = "PolyRing_poly_sub" then "PolyRing.poly_sub"
  else if f = "poly_smul" then "PolyRing.poly_smul"
  else if f = "PolyRing_poly_smul" then "PolyRing.poly_smul"
  else if f = "ntt_mul" then "PolyRing.ntt_mul"
  else if f = "PolyRing_ntt_mul" then "PolyRing.ntt_mul"
  else f

/-- Recognize an extracted `PolyRing` call node as a `PolyOp` at `(q, n, c)`:
    read the `ImpExpr.app` head, restore its trait qualifier, and dispatch
    through `recognizePolyOp`. A non-`app` node, or an unrecognized head, is
    rejected. -/
def recognizePrimeirPolyCall (e : ImpExpr) (q n : Nat) (c : ZMod q) : Option PolyOp :=
  match e with
  | .app f _ => recognizePolyOp (primeirPolyHead f) q n c
  | _ => none

@[simp] theorem recognize_nttMulCall (q n : Nat) (c : ZMod q) :
    recognizePrimeirPolyCall nttMulCall q n c = some (.nttMul q n) := rfl

@[simp] theorem recognize_polyAddCall (q n : Nat) (c : ZMod q) :
    recognizePrimeirPolyCall polyAddCall q n c = some (.polyAdd q n) := rfl

/-- The extracted `ntt_add` node is not recognized: the dialect has no op for
    it. `nttAddCom` is the composite that produces its result. -/
theorem recognize_nttAddCall (q n : Nat) (c : ZMod q) :
    recognizePrimeirPolyCall nttAddCall q n c = none := rfl

/-! ### The resolved-`impl` head form

When the emitter binds a `PolyRing` method to an `impl` the crate defines, the
call node carries `PolyRing_<m>` in place of the bare method name. Recognition
is the same on both forms, and the composite and rejection cases stay as they
are on the bare form. -/

/-- The `ntt_mul` call node as emitted with the method resolved to a local
    `impl`. -/
def nttMulCallResolved : ImpExpr := .app "PolyRing_ntt_mul" [.var "a", .var "b"]

/-- The `poly_add` call node as emitted with the methods resolved to a local
    `impl`. -/
def polyAddCallResolved : ImpExpr :=
  .app "PolyRing_poly_add" [(.app "PolyRing_intt" [(.app "PolyRing_basemul"
    [(.var "a_hat"), (.app "PolyRing_ntt" [(.var "s")])])]), (.var "e")]

/-- The `ntt_add` call node as emitted with the method resolved to a local
    `impl`. -/
def nttAddCallResolved : ImpExpr :=
  .app "PolyRing_ntt_add" [(.app "PolyRing_basemul" [(.var "a0"), (.var "v0")]),
    (.app "PolyRing_basemul" [(.var "a1"), (.var "v1")])]

@[simp] theorem recognize_nttMulCallResolved (q n : Nat) (c : ZMod q) :
    recognizePrimeirPolyCall nttMulCallResolved q n c = some (.nttMul q n) := rfl

@[simp] theorem recognize_polyAddCallResolved (q n : Nat) (c : ZMod q) :
    recognizePrimeirPolyCall polyAddCallResolved q n c = some (.polyAdd q n) := rfl

/-- The resolved `ntt_add` node is rejected for the same reason as the bare
    one. -/
theorem recognize_nttAddCallResolved (q n : Nat) (c : ZMod q) :
    recognizePrimeirPolyCall nttAddCallResolved q n c = none := rfl

/-- Recognition does not depend on which of the two head forms the emitter
    produced. -/
theorem recognize_head_forms_agree (q n : Nat) (c : ZMod q) :
    recognizePrimeirPolyCall nttMulCallResolved q n c
      = recognizePrimeirPolyCall nttMulCall q n c := rfl

/-! ## 6. The pass: recognized binary coefficient-form call → emit leaf

`poly_add`, `poly_sub` and `ntt_mul` share the binary coefficient-form leaf
shape `[polyC q n, polyC q n] → polyC q n`, so one pass covers them. The
form-crossing ops (`ntt`, `intt`) and the NTT-form `basemul` have different
contexts and use their own leaves. -/

/-- Compile an extracted binary coefficient-form `PolyRing` call to its
    `Com polyDialect` leaf; `none` if the node is not one. -/
def compilePolyBinCallC (e : ImpExpr) (q n : Nat) (c : ZMod q) :
    Option (Com polyDialect [PolyTy.polyC q n, PolyTy.polyC q n] (PolyTy.polyC q n)) :=
  match recognizePrimeirPolyCall e q n c with
  | some (.polyAdd _ _) => some (polyAddLeaf q n)
  | some (.polySub _ _) => some (polySubLeaf q n)
  | some (.nttMul _ _) => some (nttMulLeaf q n)
  | _ => none

/-- The pass emits `nttMulLeaf` for the extracted `ntt_mul` call. -/
theorem compilePolyBinCallC_nttMul (q n : Nat) (c : ZMod q) :
    compilePolyBinCallC nttMulCall q n c = some (nttMulLeaf q n) := rfl

/-- **The extracted `ntt_mul` call compiles and ties, end to end.** The call
    node of `poly_mul_demo`, run through the pass, yields the
    `Com polyDialect` leaf carrying `PolyOp.nttMul`, whose denotation is the
    ring product `realNttMul (dom q) p r`. -/
theorem primeir_poly_ntt_mul_compiles_and_ties {q n : Nat} [ND : NttDomains]
    [Fact (Nat.Prime q)] (c : ZMod q) (p r : CPolynomial (ZMod q)) :
    ∃ prog, compilePolyBinCallC nttMulCall q n c = some prog ∧
      prog.denote (.cons p (.cons r .nil)) = realNttMul (ND.dom q) p r :=
  ⟨nttMulLeaf q n, rfl, primeir_poly_ntt_mul_recognized_denote p r⟩

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxPrimeIrPoly
