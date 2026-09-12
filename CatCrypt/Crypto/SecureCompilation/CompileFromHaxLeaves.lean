/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.CompileFromHax
public import CatCrypt.Crypto.SecureCompilation.CompileFromHax

/-!
# C4: the verified compiler emits correct crypto leaves from extracted source

This module is the **C4** step of the verified-compiler plan: it demonstrates
that the verified compiler `compileFromHax` (C3) **replaces hand-authored `Com`
terms** by *emitting* them from the hax-extracted source. For each SHA-256 round
component we give the extracted-shape `ImpExpr` (let-normalized, scalar, binary
ALU + rotate, as the hax pipeline produces after ANF) and prove that compiling
it yields a jasmin `Com` whose denotation equals the FIPS 180-4 spec formula.

Unlike the C2/C3 σ₀ message-schedule demo, the leaves here are the SHA-256
**round** functions — the big sigmas `Σ₀`, `Σ₁` of the compression function and
the majority function `Maj`:

* `Σ₀(x) = (x ror 2) ⊕ (x ror 13) ⊕ (x ror 22)`            (`bigSigma0`)
* `Σ₁(x) = (x ror 6) ⊕ (x ror 11) ⊕ (x ror 25)`            (`bigSigma1`)
* `Maj(x,y,z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)`               (`maj`)

* `Ch(x,y,z) = (x ∧ y) ⊕ (¬x ∧ z)`                           (`ch`)

The `Ch` leaf uses bitwise NOT. `ImpExprToThir`'s source semantics
(`denoteScalar`/`denoteAtomExpr`) now recognise the unary `Not`/`BitNot` head as
complement at the working width (`~~~x = x ^^^ allOnes`), but the **translator**
(`rhsOf`) stays width-agnostic, so it cannot synthesise the all-ones literal.
We therefore desugar `¬x` at the source as `BitXor[x, lit (2³²−1)]`
(`2³²−1 = 4294967295`, whose width-32 denotation is `allOnes 32`), which the
existing `BitXor` recogniser handles — and prove the source denotes to the FIPS
`(x ∧ y) ⊕ (¬x ∧ z)` formula via `BitVec.xor_allOnes`.

## Method

Each leaf follows the C3 σ₀ corollary pattern (`CompileFromHax.sigma0_compiles`)
exactly:

1. A let-normalized `ImpExpr` source (`bigSigma0Src` / `bigSigma1Src` / `majSrc`),
   each operator its own `letBind` over atom arguments.
2. A source-spec lemma (`*_denoteScalar`) proving the source `denoteScalar`
   computes the FIPS formula — discharged by `simp`/`rfl` since the closed
   let-normalized body reduces.
3. A `*_isSome` lemma: the compile succeeds (`native_decide` on the closed term).
4. The leaf theorem (`*_compiles`): there is a compiled `Com jasminDialect` `c`
   with `compileFromHax … = some c` and, for every input, `c.denote = ` the FIPS
   formula — routed through the C3 per-primitive obligation
   `compileFromHax_meets_spec`. No fresh compiler reasoning per leaf.

The point: the emitted jasmin `Com` is *computed by the verified compiler from
the extracted source*, and proven to match the reference spec — the compiler,
not a human, authored the leaf.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxLeaves

open _root_.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## §1  Σ₀ — the SHA-256 compression-function big sigma 0

`Σ₀(x) = ROTR²(x) ⊕ ROTR¹³(x) ⊕ ROTR²²(x)`, at `w = 32`, one parameter `"x"`. -/

/-- The Σ₀ source as a hax `ImpExpr`, fully let-normalized, parameter `"x"`. -/
def bigSigma0Src : ImpExpr :=
  .letBind "a" (.app "rotate_right" [.var "x", .lit (.int 2)])
    (.letBind "b" (.app "rotate_right" [.var "x", .lit (.int 13)])
      (.letBind "c" (.app "rotate_right" [.var "x", .lit (.int 22)])
        (.letBind "ab" (.app "BitXor" [.var "a", .var "b"])
          (.letBind "r" (.app "BitXor" [.var "ab", .var "c"])
            (.var "r")))))

/-- The Σ₀ source denotes (under `denoteScalar`) to the FIPS 180-4 formula
    `ROTR²(x) ⊕ ROTR¹³(x) ⊕ ROTR²²(x)`. -/
theorem bigSigma0Src_denoteScalar (I : Fin 1 → BitVec 32) :
    ImpExpr.denoteScalar ["x"] I bigSigma0Src (fun _ => none)
      = some ((I 0).rotateRight 2 ^^^ (I 0).rotateRight 13 ^^^ (I 0).rotateRight 22) := by
  simp only [bigSigma0Src, ImpExpr.denoteScalar, denoteAtomExpr, recogBin, recogShift,
    litNat?, ShiftKind.apply, List.idxOf?, List.findIdx?, JasminBinOp.apply,
    reduceIte, String.reduceEq, Int.toNat]
  rfl

/-- The compile-from-hax pipeline succeeds on Σ₀ (`w = 32`, one parameter). -/
theorem bigSigma0_compileFromHax_isSome :
    (compileFromHax (w := 32) (nIn := 1) ["x"] bigSigma0Src).isSome := by
  native_decide

/-- **Σ₀ leaf emitted by the verified compiler.** There is a compiled
    `Com jasminDialect` `c` with `compileFromHax ["x"] bigSigma0Src = some c`, and
    for every input `x`, `c`'s `BitVec 32` denotation is exactly the FIPS 180-4 Σ₀
    formula `(x ror 2) ⊕ (x ror 13) ⊕ (x ror 22)`. Routed through the C3
    per-primitive obligation `compileFromHax_meets_spec`. -/
theorem bigSigma0_compiles :
    ∃ (c : Com jasminDialect (frontCtxt 32 1 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 1) ["x"] bigSigma0Src = some c ∧
      ∀ (x : BitVec 32),
        c.denote (inputValuation 32 1 (fun _ => x))
          = x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22 := by
  set c := (compileFromHax (w := 32) (nIn := 1) ["x"] bigSigma0Src).get
    bigSigma0_compileFromHax_isSome with hc_def
  have hc : compileFromHax (w := 32) (nIn := 1) ["x"] bigSigma0Src = some c :=
    (Option.some_get _).symm
  refine ⟨c, hc, ?_⟩
  intro x
  have hspec := bigSigma0Src_denoteScalar (fun _ => x)
  exact compileFromHax_meets_spec (w := 32) (nIn := 1) ["x"] (fun _ => x)
    bigSigma0Src _ hc hspec

/-! ## §2  Σ₁ — the SHA-256 compression-function big sigma 1

`Σ₁(x) = ROTR⁶(x) ⊕ ROTR¹¹(x) ⊕ ROTR²⁵(x)`, at `w = 32`, one parameter `"x"`. -/

/-- The Σ₁ source as a hax `ImpExpr`, fully let-normalized, parameter `"x"`. -/
def bigSigma1Src : ImpExpr :=
  .letBind "a" (.app "rotate_right" [.var "x", .lit (.int 6)])
    (.letBind "b" (.app "rotate_right" [.var "x", .lit (.int 11)])
      (.letBind "c" (.app "rotate_right" [.var "x", .lit (.int 25)])
        (.letBind "ab" (.app "BitXor" [.var "a", .var "b"])
          (.letBind "r" (.app "BitXor" [.var "ab", .var "c"])
            (.var "r")))))

/-- The Σ₁ source denotes (under `denoteScalar`) to the FIPS 180-4 formula
    `ROTR⁶(x) ⊕ ROTR¹¹(x) ⊕ ROTR²⁵(x)`. -/
theorem bigSigma1Src_denoteScalar (I : Fin 1 → BitVec 32) :
    ImpExpr.denoteScalar ["x"] I bigSigma1Src (fun _ => none)
      = some ((I 0).rotateRight 6 ^^^ (I 0).rotateRight 11 ^^^ (I 0).rotateRight 25) := by
  simp only [bigSigma1Src, ImpExpr.denoteScalar, denoteAtomExpr, recogBin, recogShift,
    litNat?, ShiftKind.apply, List.idxOf?, List.findIdx?, JasminBinOp.apply,
    reduceIte, String.reduceEq, Int.toNat]
  rfl

/-- The compile-from-hax pipeline succeeds on Σ₁ (`w = 32`, one parameter). -/
theorem bigSigma1_compileFromHax_isSome :
    (compileFromHax (w := 32) (nIn := 1) ["x"] bigSigma1Src).isSome := by
  native_decide

/-- **Σ₁ leaf emitted by the verified compiler.** There is a compiled
    `Com jasminDialect` `c` with `compileFromHax ["x"] bigSigma1Src = some c`, and
    for every input `x`, `c`'s `BitVec 32` denotation is exactly the FIPS 180-4 Σ₁
    formula `(x ror 6) ⊕ (x ror 11) ⊕ (x ror 25)`. Routed through the C3
    per-primitive obligation `compileFromHax_meets_spec`. -/
theorem bigSigma1_compiles :
    ∃ (c : Com jasminDialect (frontCtxt 32 1 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 1) ["x"] bigSigma1Src = some c ∧
      ∀ (x : BitVec 32),
        c.denote (inputValuation 32 1 (fun _ => x))
          = x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25 := by
  set c := (compileFromHax (w := 32) (nIn := 1) ["x"] bigSigma1Src).get
    bigSigma1_compileFromHax_isSome with hc_def
  have hc : compileFromHax (w := 32) (nIn := 1) ["x"] bigSigma1Src = some c :=
    (Option.some_get _).symm
  refine ⟨c, hc, ?_⟩
  intro x
  have hspec := bigSigma1Src_denoteScalar (fun _ => x)
  exact compileFromHax_meets_spec (w := 32) (nIn := 1) ["x"] (fun _ => x)
    bigSigma1Src _ hc hspec

/-! ## §3  Maj — the SHA-256 majority function

`Maj(x,y,z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)`, at `w = 32`, three parameters
`["x","y","z"]` (`nIn = 3`; `I 0 = x`, `I 1 = y`, `I 2 = z`). The three-input
vector is `![x, y, z]`, so `inpGet ![x,y,z] 0 = x`, etc. -/

/-- The Maj source as a hax `ImpExpr`, fully let-normalized, parameters
    `["x","y","z"]`. -/
def majSrc : ImpExpr :=
  .letBind "xy" (.app "BitAnd" [.var "x", .var "y"])
    (.letBind "xz" (.app "BitAnd" [.var "x", .var "z"])
      (.letBind "yz" (.app "BitAnd" [.var "y", .var "z"])
        (.letBind "t" (.app "BitXor" [.var "xy", .var "xz"])
          (.letBind "r" (.app "BitXor" [.var "t", .var "yz"])
            (.var "r")))))

/-- The Maj source denotes (under `denoteScalar`, parameters `["x","y","z"]`) to the
    FIPS 180-4 formula `(x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)`, reading `x = inpGet I 0`,
    `y = inpGet I 1`, `z = inpGet I 2`. -/
theorem majSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 32) :
    ImpExpr.denoteScalar ["x", "y", "z"] I majSrc (fun _ => none)
      = some ((inpGet I 0 &&& inpGet I 1) ^^^ (inpGet I 0 &&& inpGet I 2)
                ^^^ (inpGet I 1 &&& inpGet I 2)) := by
  simp only [majSrc, ImpExpr.denoteScalar, denoteAtomExpr, recogBin,
    List.idxOf?, List.findIdx?, JasminBinOp.apply,
    reduceIte, String.reduceEq]
  rfl

/-- The compile-from-hax pipeline succeeds on Maj (`w = 32`, three parameters). -/
theorem maj_compileFromHax_isSome :
    (compileFromHax (w := 32) (nIn := 3) ["x", "y", "z"] majSrc).isSome := by
  native_decide

/-- **Maj leaf emitted by the verified compiler.** There is a compiled
    `Com jasminDialect` `c` with `compileFromHax ["x","y","z"] majSrc = some c`, and
    for every triple `(x, y, z)`, `c`'s `BitVec 32` denotation (under the input
    valuation `![x, y, z]`) is exactly the FIPS 180-4 Maj formula
    `(x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)`. Routed through the C3 per-primitive obligation
    `compileFromHax_meets_spec`. -/
theorem maj_compiles :
    ∃ (c : Com jasminDialect (frontCtxt 32 3 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 3) ["x", "y", "z"] majSrc = some c ∧
      ∀ (x y z : BitVec 32),
        c.denote (inputValuation 32 3 ![x, y, z])
          = (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z) := by
  set c := (compileFromHax (w := 32) (nIn := 3) ["x", "y", "z"] majSrc).get
    maj_compileFromHax_isSome with hc_def
  have hc : compileFromHax (w := 32) (nIn := 3) ["x", "y", "z"] majSrc = some c :=
    (Option.some_get _).symm
  refine ⟨c, hc, ?_⟩
  intro x y z
  -- The FIPS Maj source-spec at `![x, y, z]`: `inpGet ![x,y,z] i` reduces to the
  -- i-th component, so the spec is the plain `(x∧y) ⊕ (x∧z) ⊕ (y∧z)`.
  have hspec : ImpExpr.denoteScalar ["x", "y", "z"] ![x, y, z] majSrc (fun _ => none)
      = some ((x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)) := by
    exact majSrc_denoteScalar (nIn := 3) ![x, y, z]
  exact compileFromHax_meets_spec (w := 32) (nIn := 3) ["x", "y", "z"] ![x, y, z]
    majSrc _ hc hspec

/-! ## §4  Ch — the SHA-256 choose function

`Ch(x,y,z) = (x ∧ y) ⊕ (¬x ∧ z)`, at `w = 32`, three parameters `["x","y","z"]`
(`nIn = 3`; `I 0 = x`, `I 1 = y`, `I 2 = z`). The complement `¬x` is desugared at
the source as `BitXor[x, lit 4294967295]` (the all-ones literal at width 32), so
the width-agnostic translator handles it via the existing `BitXor` recogniser. -/

/-- The Ch source as a hax `ImpExpr`, fully let-normalized, parameters
    `["x","y","z"]`. The complement `¬x` is the desugared `BitXor[x, ones]` where
    `ones = 0xFFFFFFFF` is first bound to its own local (a bare-literal `Rhs.atom`,
    lowered to a `regConst`) — the front rejects a bare literal as a *binary-op
    operand* (`Atom.toVar (.lit _) = none`), so the all-ones constant must be
    materialized into a register first. The v1 binary-ALU translator then accepts
    every op (all operands are now variables/inputs). -/
def chSrc : ImpExpr :=
  .letBind "ones" (.lit (.int 4294967295))
    (.letBind "nx" (.app "BitXor" [.var "x", .var "ones"])
      (.letBind "t1" (.app "BitAnd" [.var "x", .var "y"])
        (.letBind "t2" (.app "BitAnd" [.var "nx", .var "z"])
          (.letBind "r" (.app "BitXor" [.var "t1", .var "t2"])
            (.var "r")))))

/-- The Ch source denotes (under `denoteScalar`, parameters `["x","y","z"]`) to the
    FIPS 180-4 formula `(x ∧ y) ⊕ (¬x ∧ z)`, reading `x = inpGet I 0`,
    `y = inpGet I 1`, `z = inpGet I 2`. The desugared `x ^^^ 0xFFFFFFFF` collapses
    to `~~~x` via `BitVec.xor_allOnes` (`0xFFFFFFFF` denotes to `allOnes 32`). -/
theorem chSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 32) :
    ImpExpr.denoteScalar ["x", "y", "z"] I chSrc (fun _ => none)
      = some ((inpGet I 0 &&& inpGet I 1) ^^^ ((~~~ inpGet I 0) &&& inpGet I 2)) := by
  -- First reduce the let-chain (Maj-style) to the *un-rewritten* `x ^^^ ofNat …`
  -- form, then fold `ofNat 32 0xFFFFFFFF = allOnes` and `x ^^^ allOnes = ~~~x`.
  have e : ImpExpr.denoteScalar ["x", "y", "z"] I chSrc (fun _ => none)
      = some ((inpGet I 0 &&& inpGet I 1)
                ^^^ ((inpGet I 0 ^^^ BitVec.ofNat 32 4294967295) &&& inpGet I 2)) := by
    simp only [chSrc, ImpExpr.denoteScalar, denoteAtomExpr, recogBin,
      litNat?, JasminBinOp.apply, List.idxOf?, List.findIdx?,
      reduceIte, String.reduceEq, Int.toNat]
    rfl
  rw [e, show (BitVec.ofNat 32 4294967295) = BitVec.allOnes 32 from by decide,
    BitVec.xor_allOnes]

/-- The compile-from-hax pipeline succeeds on Ch (`w = 32`, three parameters). -/
theorem ch_compileFromHax_isSome :
    (compileFromHax (w := 32) (nIn := 3) ["x", "y", "z"] chSrc).isSome := by
  native_decide

/-- **Ch leaf emitted by the verified compiler.** There is a compiled
    `Com jasminDialect` `c` with `compileFromHax ["x","y","z"] chSrc = some c`, and
    for every triple `(x, y, z)`, `c`'s `BitVec 32` denotation (under the input
    valuation `![x, y, z]`) is exactly the FIPS 180-4 Ch formula
    `(x ∧ y) ⊕ (¬x ∧ z)`. Routed through the C3 per-primitive obligation
    `compileFromHax_meets_spec`. -/
theorem ch_compiles :
    ∃ (c : Com jasminDialect (frontCtxt 32 3 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 3) ["x", "y", "z"] chSrc = some c ∧
      ∀ (x y z : BitVec 32),
        c.denote (inputValuation 32 3 ![x, y, z])
          = (x &&& y) ^^^ ((~~~x) &&& z) := by
  set c := (compileFromHax (w := 32) (nIn := 3) ["x", "y", "z"] chSrc).get
    ch_compileFromHax_isSome with hc_def
  have hc : compileFromHax (w := 32) (nIn := 3) ["x", "y", "z"] chSrc = some c :=
    (Option.some_get _).symm
  refine ⟨c, hc, ?_⟩
  intro x y z
  -- The FIPS Ch source-spec at `![x, y, z]`: `inpGet ![x,y,z] i` reduces to the
  -- i-th component, so the spec is the plain `(x∧y) ⊕ (¬x∧z)`.
  have hspec : ImpExpr.denoteScalar ["x", "y", "z"] ![x, y, z] chSrc (fun _ => none)
      = some ((x &&& y) ^^^ ((~~~x) &&& z)) := by
    exact chSrc_denoteScalar (nIn := 3) ![x, y, z]
  exact compileFromHax_meets_spec (w := 32) (nIn := 3) ["x", "y", "z"] ![x, y, z]
    chSrc _ hc hspec

/-! ## §5  A bounded multi-op reduction loop — Horner polynomial evaluation

The leaves above are straight-line scalar functions. This demo is the first
**whole-function** piece: a *bounded loop*. Horner's rule for an `N`-term
polynomial is the canonical multi-op reduction (a `mul` then an `add` per
iteration):

```rust
fn horner(w: [u32; 5]) -> u32 {
    let mut acc = 0u32;
    for i in 0..4 { acc = acc.wrapping_mul(w[4]).wrapping_add(w[i]); }
    acc
}
```

i.e. `acc = (((0·x + c₀)·x + c₁)·x + c₂)·x + c₃` evaluating
`c₀·x³ + c₁·x² + c₂·x + c₃` at `x = w[4]`, coefficients `cⱼ = w[j]`. This is a
`forFold`-shaped bounded loop (single `u32` accumulator, literal bounds `0..4`).
`ImpExprToThir` §7 unrolls it into a flat `ImpExpr` let-chain — two ops with a
fresh temporary per iteration, exactly `dotTail`'s discipline — which the §3
`impExprToThir` already compiles; `hornerProgram_denoteScalar` proves the unrolled
chain denotes to the `List.foldl` Horner meaning. Here `N = 4`,
array parameter `["w"]`, `nIn = 5` (`w[0..3]` coefficients, `w[4]` the point `x`).

The demo wires that through `compileFromHax_meets_spec` exactly like `maj_compiles`:
the compiled jasmin `Com` denotes to the **explicit unrolled** `BitVec 32`
expression `((c₀·x + c₁)·x + c₂)·x + c₃`. -/

open CatCrypt.Crypto.SecureCompilation.ImpExprToThir

/-- The bounded Horner reduction as a hax `ImpExpr` `forFold`-unrolling: array
    parameter `"w"`, point `x = w[4]`, `N = 4` coefficients. The flat unrolled
    let-chain produced by `ImpExprToThir.hornerProgram`. -/
def horner4Src : ImpExpr := hornerProgram "w" 4 4

/-- The Horner source denotes (under `denoteScalar`, array parameter `["w"]`) to
    the `hornerFold` source meaning, which unfolds to the explicit
    `BitVec 32` Horner form `((c₀·x + c₁)·x + c₂)·x + c₃` with `cⱼ = inpGet I j`,
    `x = inpGet I 4`. -/
theorem horner4Src_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 32) :
    ImpExpr.denoteScalar ["w"] I horner4Src (fun _ => none)
      = some ((((inpGet I 0 * inpGet I 4 + inpGet I 1) * inpGet I 4
                  + inpGet I 2) * inpGet I 4) + inpGet I 3) := by
  rw [horner4Src, hornerProgram_denoteScalar I "w" 4 4
    (by decide)
    (fun j => by
      unfold mulH
      intro h
      apply_fun (·.toList) at h
      rw [String.toList_append] at h
      rw [show "w".toList = ['w'] from rfl, show "h".toList = ['h'] from rfl] at h
      simp at h)]
  -- Unfold the 4-step `List.foldl` over `hornerStepFn` to the explicit form.
  simp only [hornerFold, hornerStepFn, List.range_succ, List.range_zero,
    List.foldl_cons, List.foldl_nil, List.foldl_append, zero_mul, zero_add]

/-- The compile-from-hax pipeline succeeds on the Horner reduction (`w = 32`, one
    array parameter, the unrolled flat let-chain). -/
theorem horner4_compileFromHax_isSome :
    (compileFromHax (w := 32) (nIn := 5) ["w"] horner4Src).isSome := by
  native_decide

/-- **Bounded Horner reduction emitted by the verified compiler.** There is a
    compiled `Com jasminDialect` `c` with `compileFromHax ["w"] horner4Src = some c`,
    and for every input vector `c`'s `BitVec 32` denotation is exactly the explicit
    unrolled Horner form `((c₀·x + c₁)·x + c₂)·x + c₃` (`cⱼ = w[j]`, `x = w[4]`).
    This is the first *whole-function* (bounded-loop, multi-op-per-iteration)
    result, routed — like the straight-line leaves — through the C3 per-primitive
    obligation `compileFromHax_meets_spec`, with the source obligation discharged
    by the §7 unrolling-preservation theorem `hornerProgram_denoteScalar`. -/
theorem horner4_compiles :
    ∃ (c : Com jasminDialect (frontCtxt 32 5 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 5) ["w"] horner4Src = some c ∧
      ∀ (I : Fin 5 → BitVec 32),
        c.denote (inputValuation 32 5 I)
          = (((I 0 * I 4 + I 1) * I 4 + I 2) * I 4) + I 3 := by
  set c := (compileFromHax (w := 32) (nIn := 5) ["w"] horner4Src).get
    horner4_compileFromHax_isSome with hc_def
  have hc : compileFromHax (w := 32) (nIn := 5) ["w"] horner4Src = some c :=
    (Option.some_get _).symm
  refine ⟨c, hc, ?_⟩
  intro I
  -- The explicit Horner spec at `I`: `inpGet I j = I j` for `j < 5`.
  have e0 : inpGet I 0 = I 0 := by simp only [inpGet, show (0:Nat)<5 by decide, dif_pos]; congr 1
  have e1 : inpGet I 1 = I 1 := by simp only [inpGet, show (1:Nat)<5 by decide, dif_pos]; congr 1
  have e2 : inpGet I 2 = I 2 := by simp only [inpGet, show (2:Nat)<5 by decide, dif_pos]; congr 1
  have e3 : inpGet I 3 = I 3 := by simp only [inpGet, show (3:Nat)<5 by decide, dif_pos]; congr 1
  have e4 : inpGet I 4 = I 4 := by simp only [inpGet, show (4:Nat)<5 by decide, dif_pos]; congr 1
  have hspec : ImpExpr.denoteScalar ["w"] I horner4Src (fun _ => none)
      = some ((((I 0 * I 4 + I 1) * I 4 + I 2) * I 4) + I 3) := by
    rw [horner4Src_denoteScalar (nIn := 5) I, e0, e1, e2, e3, e4]
  exact compileFromHax_meets_spec (w := 32) (nIn := 5) ["w"] I horner4Src _ hc hspec

/-! ## §6  A bounded array-write recurrence — the message-schedule shape

The Horner demo (§5) carries a *single* scalar accumulator. This demo is the
**array-write** companion (`ImpExprToThir` §8): a bounded recurrence over an
*array* accumulator, where each step reads earlier array elements at literal
offsets and writes a new one — the SHA-256 **message-schedule** shape. With
literal indices, the array SSA's into per-element locals (no memory model):
`w[k]` for a not-yet-written `k` is an input seed; a written `W[k]` is a local.

The body is fixed to the canonical two-read one-add recurrence (Fibonacci-style):

```rust
fn fib(w: [u32; 2]) -> u32 {
    let mut W = [w[0], w[1], 0, 0, 0];
    for i in 2..5 { W[i] = W[i-1].wrapping_add(W[i-2]); }
    W[4]
}
```

i.e. seeds `W[0] = w[0]`, `W[1] = w[1]`, then `W[i] = W[i-1] + W[i-2]` for
`i = 2,3,4`, returning the final element `W[4]`. `ImpExprToThir` §8 unrolls this
into a flat per-element-SSA let-chain (`arrRecProgram "w" 2 5`) — each write a
fresh local reading two earlier elements (locals or input seeds) — which the §3
`impExprToThir` compiles directly; `arrRecProgram_denoteScalar` proves the chain
denotes to the `arrFold` array-state meaning via the array-SSA invariant.

The closed form: `W[2] = w[1]+w[0]`, `W[3] = W[2]+w[1]`,
`W[4] = W[3]+W[2] = ((w[1]+w[0])+w[1]) + (w[1]+w[0])`. The demo wires that through
`compileFromHax_meets_spec` exactly like the Horner / straight-line leaves. This
is the *array-write* whole-function piece; it does **not** emit the full SHA-256
σ-schedule (which needs the wider σ₀/σ₁ body), only the read-read-write floor. -/

/-- The bounded array recurrence as a hax `ImpExpr`: array parameter `"w"`,
    seed count `base = 2`, length `N = 5`. The flat per-element-SSA let-chain
    produced by `ImpExprToThir.arrRecProgram`. -/
def fibSrc : ImpExpr := arrRecProgram "w" 2 5

/-- The array parameter `"w"` is distinct from every per-element local name. -/
theorem w_ne_wName (k : Nat) : ("w" : String) ≠ wName k := by
  unfold wName
  intro hc
  apply_fun (·.toList) at hc
  rw [show ("w" : String).toList = ['w'] from rfl, String.toList_append,
      show ("W" : String).toList = ['W'] from rfl] at hc
  simp at hc

/-- The recurrence source denotes (under `denoteScalar`, array parameter `["w"]`)
    to the `arrFold` array-state meaning, which unfolds to the explicit
    `BitVec 32` form `((w[1]+w[0])+w[1]) + (w[1]+w[0])` (`w[j] = inpGet I j`). -/
theorem fibSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 32) :
    ImpExpr.denoteScalar ["w"] I fibSrc (fun _ => none)
      = some (((inpGet I 1 + inpGet I 0) + inpGet I 1) + (inpGet I 1 + inpGet I 0)) := by
  rw [fibSrc, arrRecProgram_denoteScalar I "w" 2 5 w_ne_wName (by decide) (by decide)]
  -- Unfold the 3-write `arrFold` array state at the final element `W[4]`.
  simp only [arrFold, arrStepFn, Function.update_apply]
  norm_num

/-- The compile-from-hax pipeline succeeds on the array recurrence (`w = 32`, one
    array parameter, the unrolled per-element-SSA let-chain). -/
theorem fib_compileFromHax_isSome :
    (compileFromHax (w := 32) (nIn := 2) ["w"] fibSrc).isSome := by
  native_decide

/-- **Bounded array-write recurrence emitted by the verified compiler.** There is
    a compiled `Com jasminDialect` `c` with `compileFromHax ["w"] fibSrc = some c`,
    and for every input the `BitVec 32` denotation is exactly the explicit
    message-schedule-shape form `((w[1]+w[0])+w[1]) + (w[1]+w[0])` — the final
    element `W[4]` of `W[i] = W[i-1] + W[i-2]` seeded from `w[0], w[1]`. This is
    the *array-write* whole-function result (per-element SSA, two reads + one op
    per write), routed — like the straight-line leaves — through the C3
    per-primitive obligation `compileFromHax_meets_spec`, with the source
    obligation discharged by the §8 preservation theorem
    `arrRecProgram_denoteScalar`. -/
theorem fib_compiles :
    ∃ (c : Com jasminDialect (frontCtxt 32 2 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 2) ["w"] fibSrc = some c ∧
      ∀ (I : Fin 2 → BitVec 32),
        c.denote (inputValuation 32 2 I)
          = ((I 1 + I 0) + I 1) + (I 1 + I 0) := by
  set c := (compileFromHax (w := 32) (nIn := 2) ["w"] fibSrc).get
    fib_compileFromHax_isSome with hc_def
  have hc : compileFromHax (w := 32) (nIn := 2) ["w"] fibSrc = some c :=
    (Option.some_get _).symm
  refine ⟨c, hc, ?_⟩
  intro I
  have e0 : inpGet I 0 = I 0 := by simp only [inpGet, show (0:Nat)<2 by decide, dif_pos]; congr 1
  have e1 : inpGet I 1 = I 1 := by simp only [inpGet, show (1:Nat)<2 by decide, dif_pos]; congr 1
  have hspec : ImpExpr.denoteScalar ["w"] I fibSrc (fun _ => none)
      = some (((I 1 + I 0) + I 1) + (I 1 + I 0)) := by
    rw [fibSrc_denoteScalar (nIn := 2) I, e0, e1]
  exact compileFromHax_meets_spec (w := 32) (nIn := 2) ["w"] I fibSrc _ hc hspec

/-! ## §7  The real SHA-256 message-schedule σ recurrence (the convergence demo)

This is **the convergence demo**: the §6 array-write recurrence (per-element SSA)
combined with a multi-op σ step body, giving the **SHA-256 message
schedule** (FIPS 180-4 §6.2.2), value-preserving from hax `ImpExpr` through the
compiler to jasmin. Where §6 fixed the step to `W[i-1]+W[i-2]`, here the step is
the full four-read σ body:

```text
W[i] = σ₁(W[i-2]) + W[i-7] + σ₀(W[i-15]) + W[i-16]      (i = 16 .. N-1, wrapping)
σ₀(x) = (x ⋙ 7)  ⊕ (x ⋙ 18) ⊕ (x >> 3)
σ₁(x) = (x ⋙ 17) ⊕ (x ⋙ 19) ⊕ (x >> 10)
```

with `W[0..15]` the input message words. `ImpExprToThir` §9 unrolls this into a
flat per-element-SSA let-chain (`schedProgram 18`): each write computes σ₁/σ₀ (the
rotate/shift/xor let-chains the §5/§7 leaves already prove) into scratch locals,
then the three wrapping adds, binding a fresh per-element local. The §9
`schedProgram_denoteScalar` proves the chain denotes to the `schedFold`
array-state meaning, via the same array-SSA invariant as §6 carried over the wider
σ step.

We take `N = 18`, so the schedule computes two new words `W[16]`, `W[17]` past the
16 input words, returning `W[17]`. All four reads for `W[17]` (`W[15]`, `W[10]`,
`W[2]`, `W[1]`) are input words (`< 16`), so the closed form is purely in the
inputs:

```text
W[17] = σ₁(w[15]) + w[10] + σ₀(w[2]) + w[1].
```

No new dialect op, no hardware leaf: the **whole** machinery is the §6 array-SSA
recurrence plus the §5/§7 σ leaves. Scope: this is a small-`N` slice (two
schedule words) exercising exactly the mechanism the full 64-round `W` uses — the
same `schedProgram`/`schedProgram_denoteScalar` at `N = 64`, just a heavier
`isSome` compute. -/

/-- The bounded σ schedule as a hax `ImpExpr`: 16 input message words (`nIn = 16`,
    array parameter `"w"`), length `N = 18` (compute `W[16]`, `W[17]`). The flat
    per-element-SSA σ let-chain produced by `ImpExprToThir.schedProgram`. -/
def schedSrc : ImpExpr := schedProgram 18

/-- The σ-schedule source denotes (under `denoteScalar`, array parameter `["w"]`)
    to the `schedFold` array state at `W[17]`, which unfolds to the
    explicit FIPS form `σ₁(w[15]) + w[10] + σ₀(w[2]) + w[1]` (`w[j] = inpGet I j`).
    The σ₁/σ₀ of the specific input words `w[15]`/`w[2]` are the
    multi-op step the §6 fixed-body recurrence did not reach. -/
theorem schedSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 32) :
    ImpExpr.denoteScalar ["w"] I schedSrc (fun _ => none)
      = some (sigma1Fn (inpGet I 15) + inpGet I 10 + sigma0Fn (inpGet I 2) + inpGet I 1) := by
  rw [schedSrc, schedProgram_denoteScalar I 18 (by decide)]
  -- Unfold the 2-write `schedFold` array state at the final element `W[17]`.
  simp only [schedFold, schedStepFn, Function.update_apply]
  rfl

/-- The compile-from-hax pipeline succeeds on the σ schedule (`w = 32`, 16 input
    words, the unrolled per-element-SSA σ let-chain). The compute is small (two
    schedule writes), so the `isSome` decides cheaply. -/
theorem sched_compileFromHax_isSome :
    (compileFromHax (w := 32) (nIn := 16) ["w"] schedSrc).isSome := by
  native_decide

/-- **The real SHA-256 message-schedule σ recurrence, emitted by the verified
    compiler.** There is a compiled `Com jasminDialect` `c` with
    `compileFromHax ["w"] schedSrc = some c`, and for every 16-word input the
    `BitVec 32` denotation is exactly the FIPS 180-4 closed form
    `σ₁(w[15]) + w[10] + σ₀(w[2]) + w[1]` — the schedule word `W[17]` of
    `W[i] = σ₁(W[i-2]) + W[i-7] + σ₀(W[i-15]) + W[i-16]` seeded from the 16 input
    words. This is the **convergence**: the §6 array-write per-element SSA combined
    with the §5/§7 multi-op σ body (rotate/shift/xor + three adds). Routed — like
    every leaf — through the C3 obligation `compileFromHax_meets_spec`, with the
    source obligation discharged by the §9 preservation theorem
    `schedProgram_denoteScalar`. A small-`N` (two-word) slice of the full 64-round
    schedule, demonstrating the mechanism end to end. -/
theorem sched_compiles :
    ∃ (c : Com jasminDialect (frontCtxt 32 16 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 16) ["w"] schedSrc = some c ∧
      ∀ (I : Fin 16 → BitVec 32),
        c.denote (inputValuation 32 16 I)
          = sigma1Fn (I 15) + I 10 + sigma0Fn (I 2) + I 1 := by
  set c := (compileFromHax (w := 32) (nIn := 16) ["w"] schedSrc).get
    sched_compileFromHax_isSome with hc_def
  have hc : compileFromHax (w := 32) (nIn := 16) ["w"] schedSrc = some c :=
    (Option.some_get _).symm
  refine ⟨c, hc, ?_⟩
  intro I
  have e15 : inpGet I 15 = I 15 := by
    simp only [inpGet, show (15:Nat) < 16 by decide, dif_pos]; congr 1
  have e10 : inpGet I 10 = I 10 := by
    simp only [inpGet, show (10:Nat) < 16 by decide, dif_pos]; congr 1
  have e2 : inpGet I 2 = I 2 := by
    simp only [inpGet, show (2:Nat) < 16 by decide, dif_pos]; congr 1
  have e1 : inpGet I 1 = I 1 := by
    simp only [inpGet, show (1:Nat) < 16 by decide, dif_pos]; congr 1
  have hspec : ImpExpr.denoteScalar ["w"] I schedSrc (fun _ => none)
      = some (sigma1Fn (I 15) + I 10 + sigma0Fn (I 2) + I 1) := by
    rw [schedSrc_denoteScalar (nIn := 16) I, e15, e10, e2, e1]
  exact compileFromHax_meets_spec (w := 32) (nIn := 16) ["w"] I schedSrc _ hc hspec

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxLeaves
