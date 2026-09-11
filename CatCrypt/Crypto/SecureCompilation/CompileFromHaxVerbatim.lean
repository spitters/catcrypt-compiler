/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
import all CatCrypt.Crypto.SecureCompilation.ImpExprToThir
import all CatCrypt.Crypto.SecureCompilation.ThirToComFront
import all CatCrypt.Crypto.SecureCompilation.CompileFromHax
import all CatCrypt.Crypto.SHA256.Extraction.Sha256_haxpipe
public meta import CatCrypt.Crypto.SecureCompilation.CompileFromHax
public import CatCrypt.Crypto.SecureCompilation.CompileFromHax
public meta import CatCrypt.Crypto.SHA256.Extraction.Sha256_haxpipe
public import CatCrypt.Crypto.SHA256.Extraction.Sha256_haxpipe

/-!
# Compiling a verbatim hax extraction (SHA-256 σ₀)

`CompileFromHax.sigma0_compiles` compiled a *hand-written, already let-normalized*
σ₀ `ImpExpr` (`sigma0Src`). This file goes one step further and compiles the
**verbatim** hax extraction literal `Sha256.small_sigma0_impExpr`, taken exactly
as the typed extraction pipeline emits it in
`CatCrypt/Crypto/SHA256/Extraction/Sha256_haxpipe.lean`:

```text
small_sigma0_impExpr =
  letBind "x" (var "x")
    (BitXor#32 [ BitXor#32 [ rotate_right#32[x,7], rotate_right#32[x,18] ],
                 Shr#32[x,3] ])
```

That literal has the two features the §3 `impExprToThir` translator rejects:
width-suffixed heads (`BitXor#32`, `rotate_right#32`, `Shr#32`) and **nested-app
arguments** (`BitXor#32[…]` sits where an atom is required). The
`ImpExprToThir.anfLift` pre-pass (§10) closes both: it head-normalizes via
`stripWidthSuffix` and flattens nested args into fresh `letBind`s, landing the
body in the §3 atom-arg subset. The result then compiles through the *unchanged*
`compileFromHax` (C2 ∘ C1) and is value-preserving against the FIPS 180-4 σ₀
formula `(x ⋙ 7) ⊕ (x ⋙ 18) ⊕ (x ≫ 3)`.

## On the preservation statement

A naive `denoteScalar (anfLift e) = denoteScalar e` is **not** the right claim
here: the verbatim `e` has `#32`-tagged heads and nested-app args, so its *own*
`ImpExpr.denoteScalar` is `none` (the §2 source semantics, like §3, only
recognizes bare heads with atom args). `anfLift` is what *gives* the body a
denotation. The honest preservation is therefore the σ₀-specific
`anfLift_small_sigma0_denoteScalar`: the ANF-lifted verbatim body denotes to the
FIPS σ₀ value. Routed through `compileFromHax_meets_spec`, this yields
`small_sigma0_verbatim_compiles` — a verbatim-extracted body compiled correctly
end to end.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxVerbatim

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect JasminBinOp)

/-- The ANF-lifted normal form of the verbatim `Sha256.small_sigma0_impExpr`:
    head-normalized (`#32` tags dropped, `Shr → shr`) and flattened — each
    operator application now has only atom (`var`/`lit`) arguments, hoisted
    through fresh `_anf<n>` binders. This is exactly the §3 let-normalized
    atom-arg subset. (The argument counter visits the last arg first, hence the
    `_anf2, _anf1, _anf3, _anf0` ordering; each binder is used after it is
    defined.) -/
def sigma0Norm : ImpExpr :=
  .letBind "x" (.var "x")
   (.letBind "_anf2" (.app "rotate_right" [.var "x", .lit (.int 7)])
    (.letBind "_anf1" (.app "rotate_right" [.var "x", .lit (.int 18)])
     (.letBind "_anf3" (.app "BitXor" [.var "_anf2", .var "_anf1"])
      (.letBind "_anf0" (.app "shr" [.var "x", .lit (.int 3)])
       (.app "BitXor" [.var "_anf3", .var "_anf0"])))))

/-- `anfLift` of the verbatim extraction literal reduces (definitionally) to the
    explicit let-normalized `sigma0Norm`. Closed-term computation: `rfl`. -/
private theorem anfLift_small_sigma0_eq :
    anfLift Sha256.small_sigma0_impExpr = sigma0Norm := rfl

/-- **The ANF-lifted verbatim σ₀ body is value-preserving.** Its `denoteScalar`
    (the §2 source semantics, parameter `"x"`, single input `I 0 = x`) is exactly
    the FIPS 180-4 σ₀ value `(x ⋙ 7) ⊕ (x ⋙ 18) ⊕ (x ≫ 3)`. The honest
    preservation result for the verbatim extraction: the `#32`-tagged nested-app
    literal has no denotation of its own, and `anfLift` is what makes it denote —
    to the σ₀ spec. Proved by `denoteScalar`-reduction of `sigma0Norm`. -/
theorem anfLift_small_sigma0_denoteScalar (x : BitVec 32) :
    ImpExpr.denoteScalar (w := 32) (nIn := 1) ["x"] (fun _ => x)
        (anfLift Sha256.small_sigma0_impExpr) (fun _ => none)
      = some (x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ x >>> (3 : Nat)) := by
  rw [anfLift_small_sigma0_eq]
  simp only [sigma0Norm, ImpExpr.denoteScalar, denoteAtomExpr, recogBin, recogShift,
    litNat?, ShiftKind.apply, List.idxOf?, List.findIdx?, JasminBinOp.apply,
    reduceIte, String.reduceEq, Int.toNat]
  rfl

/-- The compile-from-hax pipeline succeeds on the ANF-lifted verbatim σ₀. -/
theorem small_sigma0_verbatim_isSome :
    (compileFromHax (w := 32) (nIn := 1) ["x"]
      (anfLift Sha256.small_sigma0_impExpr)).isSome := by
  rw [anfLift_small_sigma0_eq]; native_decide

/-- **A verbatim hax extraction compiles correctly.** There is a compiled
    `Com jasminDialect` `c` such that the verbatim `Sha256.small_sigma0_impExpr`
    literal — `#32`-tagged heads, nested-app arguments, leading `let x = x`,
    taken exactly as the typed extraction pipeline emits it — `anfLift`-compiles
    to `c`, and for every input `x`, `c`'s `BitVec 32` denotation is exactly the
    FIPS 180-4 σ₀ formula `(x ⋙ 7) ⊕ (x ⋙ 18) ⊕ (x ≫ 3)`. The headline
    verbatim-extraction result: routes `anfLift_small_sigma0_denoteScalar`
    through the C3 meta-theorem `compileFromHax_meets_spec` (no fresh compiler
    proof). -/
theorem small_sigma0_verbatim_compiles :
    ∃ c, compileFromHax (w := 32) (nIn := 1) ["x"]
           (anfLift Sha256.small_sigma0_impExpr) = some c ∧
         ∀ (x : BitVec 32),
           c.denote (inputValuation 32 1 (fun _ => x))
             = x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ x >>> (3 : Nat) := by
  set c := (compileFromHax (w := 32) (nIn := 1) ["x"]
    (anfLift Sha256.small_sigma0_impExpr)).get small_sigma0_verbatim_isSome with hc_def
  have hc : compileFromHax (w := 32) (nIn := 1) ["x"]
      (anfLift Sha256.small_sigma0_impExpr) = some c := (Option.some_get _).symm
  refine ⟨c, hc, ?_⟩
  intro x
  exact compileFromHax_meets_spec (w := 32) (nIn := 1) ["x"] (fun _ => x)
    (anfLift Sha256.small_sigma0_impExpr) _ hc (anfLift_small_sigma0_denoteScalar x)

/-! ## The verbatim-extraction path generalizes across the round-component family

The σ₀ demo above is not a one-off. The same `anfLift` pre-pass + unchanged
`compileFromHax` route compiles **every** verbatim SHA-256 round-component literal
the typed extraction pipeline emits — each carrying the same two §3-rejected
features (width-suffixed heads, nested-app arguments). Below: the four remaining
mixing functions (`σ₁`, `Σ₀`, `Σ₁`, and the 3-input `Maj`), each proved
value-preserving against its FIPS 180-4 formula and compiled end to end through
the same C3 meta-theorem `compileFromHax_meets_spec`. The `_anf<n>` binder
ordering is again produced by `anfLift`'s arg-counter traversal (last arg first),
confirmed per shape by the `anfLift_*_eq := rfl` probe. -/

/-! ### σ₁ — `(x ⋙ 17) ⊕ (x ⋙ 19) ⊕ (x ≫ 10)` (same shape as σ₀, constants 17/19/10) -/

/-- ANF-lifted normal form of the verbatim `Sha256.small_sigma1_impExpr`:
    identical shape to `sigma0Norm`, constants `17/19/10`. -/
def sigma1Norm : ImpExpr :=
  .letBind "x" (.var "x")
   (.letBind "_anf2" (.app "rotate_right" [.var "x", .lit (.int 17)])
    (.letBind "_anf1" (.app "rotate_right" [.var "x", .lit (.int 19)])
     (.letBind "_anf3" (.app "BitXor" [.var "_anf2", .var "_anf1"])
      (.letBind "_anf0" (.app "shr" [.var "x", .lit (.int 10)])
       (.app "BitXor" [.var "_anf3", .var "_anf0"])))))

/-- `anfLift` of the verbatim σ₁ literal reduces (definitionally) to `sigma1Norm`. -/
private theorem anfLift_small_sigma1_eq :
    anfLift Sha256.small_sigma1_impExpr = sigma1Norm := rfl

/-- The ANF-lifted verbatim σ₁ body denotes to the FIPS 180-4 σ₁ value
    `(x ⋙ 17) ⊕ (x ⋙ 19) ⊕ (x ≫ 10)`. -/
theorem anfLift_small_sigma1_denoteScalar (x : BitVec 32) :
    ImpExpr.denoteScalar (w := 32) (nIn := 1) ["x"] (fun _ => x)
        (anfLift Sha256.small_sigma1_impExpr) (fun _ => none)
      = some (x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ x >>> (10 : Nat)) := by
  rw [anfLift_small_sigma1_eq]
  simp only [sigma1Norm, ImpExpr.denoteScalar, denoteAtomExpr, recogBin, recogShift,
    litNat?, ShiftKind.apply, List.idxOf?, List.findIdx?, JasminBinOp.apply,
    reduceIte, String.reduceEq, Int.toNat]
  rfl

/-- The compile-from-hax pipeline succeeds on the ANF-lifted verbatim σ₁. -/
theorem small_sigma1_verbatim_isSome :
    (compileFromHax (w := 32) (nIn := 1) ["x"]
      (anfLift Sha256.small_sigma1_impExpr)).isSome := by
  rw [anfLift_small_sigma1_eq]; native_decide

/-- **The verbatim σ₁ extraction compiles correctly.** There is a compiled
    `Com jasminDialect` `c` with `compileFromHax ["x"] (anfLift small_sigma1) = some c`,
    and for every `x`, `c`'s `BitVec 32` denotation is exactly the FIPS 180-4 σ₁
    formula `(x ⋙ 17) ⊕ (x ⋙ 19) ⊕ (x ≫ 10)`. Routed through
    `compileFromHax_meets_spec`. -/
theorem small_sigma1_verbatim_compiles :
    ∃ c, compileFromHax (w := 32) (nIn := 1) ["x"]
           (anfLift Sha256.small_sigma1_impExpr) = some c ∧
         ∀ (x : BitVec 32),
           c.denote (inputValuation 32 1 (fun _ => x))
             = x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ x >>> (10 : Nat) := by
  set c := (compileFromHax (w := 32) (nIn := 1) ["x"]
    (anfLift Sha256.small_sigma1_impExpr)).get small_sigma1_verbatim_isSome with hc_def
  have hc : compileFromHax (w := 32) (nIn := 1) ["x"]
      (anfLift Sha256.small_sigma1_impExpr) = some c := (Option.some_get _).symm
  refine ⟨c, hc, ?_⟩
  intro x
  exact compileFromHax_meets_spec (w := 32) (nIn := 1) ["x"] (fun _ => x)
    (anfLift Sha256.small_sigma1_impExpr) _ hc (anfLift_small_sigma1_denoteScalar x)

/-! ### Σ₀ — `(x ⋙ 2) ⊕ (x ⋙ 13) ⊕ (x ⋙ 22)` (three rotates, no shift) -/

/-- ANF-lifted normal form of the verbatim `Sha256.big_sigma0_impExpr`: three
    rotates (no shift), constants `2/13/22`, hoisted through fresh `_anf<n>`
    binders in the arg-counter order. -/
def bigSigma0Norm : ImpExpr :=
  .letBind "x" (.var "x")
   (.letBind "_anf2" (.app "rotate_right" [.var "x", .lit (.int 2)])
    (.letBind "_anf1" (.app "rotate_right" [.var "x", .lit (.int 13)])
     (.letBind "_anf3" (.app "BitXor" [.var "_anf2", .var "_anf1"])
      (.letBind "_anf0" (.app "rotate_right" [.var "x", .lit (.int 22)])
       (.app "BitXor" [.var "_anf3", .var "_anf0"])))))

/-- `anfLift` of the verbatim Σ₀ literal reduces (definitionally) to `bigSigma0Norm`. -/
private theorem anfLift_big_sigma0_eq :
    anfLift Sha256.big_sigma0_impExpr = bigSigma0Norm := rfl

/-- The ANF-lifted verbatim Σ₀ body denotes to the FIPS 180-4 Σ₀ value
    `(x ⋙ 2) ⊕ (x ⋙ 13) ⊕ (x ⋙ 22)`. -/
theorem anfLift_big_sigma0_denoteScalar (x : BitVec 32) :
    ImpExpr.denoteScalar (w := 32) (nIn := 1) ["x"] (fun _ => x)
        (anfLift Sha256.big_sigma0_impExpr) (fun _ => none)
      = some (x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22) := by
  rw [anfLift_big_sigma0_eq]
  simp only [bigSigma0Norm, ImpExpr.denoteScalar, denoteAtomExpr, recogBin, recogShift,
    litNat?, ShiftKind.apply, List.idxOf?, List.findIdx?, JasminBinOp.apply,
    reduceIte, String.reduceEq, Int.toNat]
  rfl

/-- The compile-from-hax pipeline succeeds on the ANF-lifted verbatim Σ₀. -/
theorem big_sigma0_verbatim_isSome :
    (compileFromHax (w := 32) (nIn := 1) ["x"]
      (anfLift Sha256.big_sigma0_impExpr)).isSome := by
  rw [anfLift_big_sigma0_eq]; native_decide

/-- **The verbatim Σ₀ extraction compiles correctly.** There is a compiled
    `Com jasminDialect` `c` with `compileFromHax ["x"] (anfLift big_sigma0) = some c`,
    and for every `x`, `c`'s `BitVec 32` denotation is exactly the FIPS 180-4 Σ₀
    formula `(x ⋙ 2) ⊕ (x ⋙ 13) ⊕ (x ⋙ 22)`. Routed through
    `compileFromHax_meets_spec`. -/
theorem big_sigma0_verbatim_compiles :
    ∃ c, compileFromHax (w := 32) (nIn := 1) ["x"]
           (anfLift Sha256.big_sigma0_impExpr) = some c ∧
         ∀ (x : BitVec 32),
           c.denote (inputValuation 32 1 (fun _ => x))
             = x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22 := by
  set c := (compileFromHax (w := 32) (nIn := 1) ["x"]
    (anfLift Sha256.big_sigma0_impExpr)).get big_sigma0_verbatim_isSome with hc_def
  have hc : compileFromHax (w := 32) (nIn := 1) ["x"]
      (anfLift Sha256.big_sigma0_impExpr) = some c := (Option.some_get _).symm
  refine ⟨c, hc, ?_⟩
  intro x
  exact compileFromHax_meets_spec (w := 32) (nIn := 1) ["x"] (fun _ => x)
    (anfLift Sha256.big_sigma0_impExpr) _ hc (anfLift_big_sigma0_denoteScalar x)

/-! ### Σ₁ — `(x ⋙ 6) ⊕ (x ⋙ 11) ⊕ (x ⋙ 25)` (three rotates, constants 6/11/25) -/

/-- ANF-lifted normal form of the verbatim `Sha256.big_sigma1_impExpr`: three
    rotates, constants `6/11/25`. -/
def bigSigma1Norm : ImpExpr :=
  .letBind "x" (.var "x")
   (.letBind "_anf2" (.app "rotate_right" [.var "x", .lit (.int 6)])
    (.letBind "_anf1" (.app "rotate_right" [.var "x", .lit (.int 11)])
     (.letBind "_anf3" (.app "BitXor" [.var "_anf2", .var "_anf1"])
      (.letBind "_anf0" (.app "rotate_right" [.var "x", .lit (.int 25)])
       (.app "BitXor" [.var "_anf3", .var "_anf0"])))))

/-- `anfLift` of the verbatim Σ₁ literal reduces (definitionally) to `bigSigma1Norm`. -/
private theorem anfLift_big_sigma1_eq :
    anfLift Sha256.big_sigma1_impExpr = bigSigma1Norm := rfl

/-- The ANF-lifted verbatim Σ₁ body denotes to the FIPS 180-4 Σ₁ value
    `(x ⋙ 6) ⊕ (x ⋙ 11) ⊕ (x ⋙ 25)`. -/
theorem anfLift_big_sigma1_denoteScalar (x : BitVec 32) :
    ImpExpr.denoteScalar (w := 32) (nIn := 1) ["x"] (fun _ => x)
        (anfLift Sha256.big_sigma1_impExpr) (fun _ => none)
      = some (x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25) := by
  rw [anfLift_big_sigma1_eq]
  simp only [bigSigma1Norm, ImpExpr.denoteScalar, denoteAtomExpr, recogBin, recogShift,
    litNat?, ShiftKind.apply, List.idxOf?, List.findIdx?, JasminBinOp.apply,
    reduceIte, String.reduceEq, Int.toNat]
  rfl

/-- The compile-from-hax pipeline succeeds on the ANF-lifted verbatim Σ₁. -/
theorem big_sigma1_verbatim_isSome :
    (compileFromHax (w := 32) (nIn := 1) ["x"]
      (anfLift Sha256.big_sigma1_impExpr)).isSome := by
  rw [anfLift_big_sigma1_eq]; native_decide

/-- **The verbatim Σ₁ extraction compiles correctly.** There is a compiled
    `Com jasminDialect` `c` with `compileFromHax ["x"] (anfLift big_sigma1) = some c`,
    and for every `x`, `c`'s `BitVec 32` denotation is exactly the FIPS 180-4 Σ₁
    formula `(x ⋙ 6) ⊕ (x ⋙ 11) ⊕ (x ⋙ 25)`. Routed through
    `compileFromHax_meets_spec`. -/
theorem big_sigma1_verbatim_compiles :
    ∃ c, compileFromHax (w := 32) (nIn := 1) ["x"]
           (anfLift Sha256.big_sigma1_impExpr) = some c ∧
         ∀ (x : BitVec 32),
           c.denote (inputValuation 32 1 (fun _ => x))
             = x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25 := by
  set c := (compileFromHax (w := 32) (nIn := 1) ["x"]
    (anfLift Sha256.big_sigma1_impExpr)).get big_sigma1_verbatim_isSome with hc_def
  have hc : compileFromHax (w := 32) (nIn := 1) ["x"]
      (anfLift Sha256.big_sigma1_impExpr) = some c := (Option.some_get _).symm
  refine ⟨c, hc, ?_⟩
  intro x
  exact compileFromHax_meets_spec (w := 32) (nIn := 1) ["x"] (fun _ => x)
    (anfLift Sha256.big_sigma1_impExpr) _ hc (anfLift_big_sigma1_denoteScalar x)

/-! ### Maj — `(a ∧ b) ⊕ (a ∧ c) ⊕ (b ∧ c)` (3-input, `BitAnd`-tree) -/

/-- ANF-lifted normal form of the verbatim `Sha256.maj_impExpr`: the three
    parameter binders `a/b/c` stay, then the `BitAnd`/`BitXor` tree is flattened
    into fresh `_anf<n>` binders (arg-counter order: `_anf2 = a∧b`, `_anf1 = a∧c`,
    `_anf3 = _anf2 ⊕ _anf1`, `_anf0 = b∧c`). -/
def majNorm : ImpExpr :=
  .letBind "a" (.var "a")
   (.letBind "b" (.var "b")
    (.letBind "c" (.var "c")
     (.letBind "_anf2" (.app "BitAnd" [.var "a", .var "b"])
      (.letBind "_anf1" (.app "BitAnd" [.var "a", .var "c"])
       (.letBind "_anf3" (.app "BitXor" [.var "_anf2", .var "_anf1"])
        (.letBind "_anf0" (.app "BitAnd" [.var "b", .var "c"])
         (.app "BitXor" [.var "_anf3", .var "_anf0"])))))))

/-- `anfLift` of the verbatim Maj literal reduces (definitionally) to `majNorm`. -/
private theorem anfLift_maj_eq :
    anfLift Sha256.maj_impExpr = majNorm := rfl

/-- The ANF-lifted verbatim Maj body denotes (parameters `["a","b","c"]`,
    `a = inpGet I 0`, `b = inpGet I 1`, `c = inpGet I 2`) to the FIPS 180-4 Maj
    value `(a ∧ b) ⊕ (a ∧ c) ⊕ (b ∧ c)`. -/
theorem anfLift_maj_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 32) :
    ImpExpr.denoteScalar (w := 32) (nIn := nIn) ["a", "b", "c"] I
        (anfLift Sha256.maj_impExpr) (fun _ => none)
      = some ((inpGet I 0 &&& inpGet I 1) ^^^ (inpGet I 0 &&& inpGet I 2)
                ^^^ (inpGet I 1 &&& inpGet I 2)) := by
  rw [anfLift_maj_eq]
  simp only [majNorm, ImpExpr.denoteScalar, denoteAtomExpr, recogBin,
    List.idxOf?, List.findIdx?, JasminBinOp.apply,
    reduceIte, String.reduceEq]
  rfl

/-- The compile-from-hax pipeline succeeds on the ANF-lifted verbatim Maj
    (`w = 32`, three parameters). -/
theorem maj_verbatim_isSome :
    (compileFromHax (w := 32) (nIn := 3) ["a", "b", "c"]
      (anfLift Sha256.maj_impExpr)).isSome := by
  rw [anfLift_maj_eq]; native_decide

/-- **The verbatim 3-input Maj extraction compiles correctly.** There is a
    compiled `Com jasminDialect` `c` with
    `compileFromHax ["a","b","c"] (anfLift maj) = some c`, and for every triple
    `(a, b, c)`, `c`'s `BitVec 32` denotation (under the input valuation
    `![a, b, c]`) is exactly the FIPS 180-4 Maj formula `(a ∧ b) ⊕ (a ∧ c) ⊕ (b ∧ c)`.
    Mirrors the `CompileFromHaxLeaves.maj_compiles` 3-input idiom and routes the
    spec through `compileFromHax_meets_spec`. -/
theorem maj_verbatim_compiles :
    ∃ c, compileFromHax (w := 32) (nIn := 3) ["a", "b", "c"]
           (anfLift Sha256.maj_impExpr) = some c ∧
         ∀ (a b c' : BitVec 32),
           c.denote (inputValuation 32 3 ![a, b, c'])
             = (a &&& b) ^^^ (a &&& c') ^^^ (b &&& c') := by
  set cc := (compileFromHax (w := 32) (nIn := 3) ["a", "b", "c"]
    (anfLift Sha256.maj_impExpr)).get maj_verbatim_isSome with hc_def
  have hc : compileFromHax (w := 32) (nIn := 3) ["a", "b", "c"]
      (anfLift Sha256.maj_impExpr) = some cc := (Option.some_get _).symm
  refine ⟨cc, hc, ?_⟩
  intro a b c'
  have hspec : ImpExpr.denoteScalar (w := 32) (nIn := 3) ["a", "b", "c"] ![a, b, c']
      (anfLift Sha256.maj_impExpr) (fun _ => none)
      = some ((a &&& b) ^^^ (a &&& c') ^^^ (b &&& c')) := by
    have h := anfLift_maj_denoteScalar (nIn := 3) ![a, b, c']
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using! h
  exact compileFromHax_meets_spec (w := 32) (nIn := 3) ["a", "b", "c"] ![a, b, c']
    (anfLift Sha256.maj_impExpr) _ hc hspec

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxVerbatim
