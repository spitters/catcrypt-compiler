/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.CompileFromHax
public import CatCrypt.Crypto.SecureCompilation.CompileFromHax

/-!
# C4: width-64 SHA-512 round leaves emitted from extracted source

This module is the **width-64** companion to `CompileFromHaxLeaves` (§3 `Maj`,
§4 `Ch`). It demonstrates that the verified compiler `compileFromHax` — and the
`ImpExprToThir` front it sits on — is **width-generic**: the very same
recognizers that emit the SHA-256 (`w = 32`) round components also emit their
SHA-512 (`w = 64`) analogues, with no front change. The leaves are the SHA-512
majority and choose functions, identical in shape to FIPS 180-4's SHA-256 round
functions but at the 64-bit working width:

* `Maj(x,y,z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)`               (`majSrc64`)
* `Ch(x,y,z) = (x ∧ y) ⊕ (¬x ∧ z)`                          (`chSrc64`)

As at `w = 32`, the `Ch` leaf's bitwise NOT is desugared at the source as
`BitXor[x, lit (2⁶⁴−1)]` (`2⁶⁴−1 = 18446744073709551615`, whose width-64
denotation is `allOnes 64`): the width-agnostic translator (`rhsOf`) cannot
synthesise an all-ones literal, so the constant is materialized into its own
local, and the source `denoteScalar` is folded to the FIPS `(x ∧ y) ⊕ (¬x ∧ z)`
formula via `BitVec.xor_allOnes`.

## Method

Each leaf follows the C3/C4 pattern (`CompileFromHaxLeaves.maj_compiles` /
`ch_compiles`) exactly, only with `w := 64`:

1. A let-normalized `ImpExpr` source (`majSrc64` / `chSrc64`), each operator its
   own `letBind` over atom arguments.
2. A source-spec lemma (`*_denoteScalar`) proving the source `denoteScalar`
   computes the FIPS formula — discharged by `simp`/`rfl` (Ch's via the
   all-ones fold).
3. A `*_isSome` lemma: the compile succeeds (`native_decide` on the closed term).
4. The leaf theorem (`*512_compiles`): there is a compiled `Com jasminDialect`
   `c` with `compileFromHax … = some c` and, for every input, `c.denote = ` the
   FIPS formula — routed through the C3 per-primitive obligation
   `compileFromHax_meets_spec`. No fresh compiler reasoning per leaf.

The point: the same front recognizes the same idioms at 64 bits, so the
SHA-512 round components join the C4 leaf set on the strength of the existing
width-generic translator.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxSha512

open _root_.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## §1  Maj — the SHA-512 majority function (`w = 64`)

`Maj(x,y,z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)`, at `w = 64`, three parameters
`["x","y","z"]` (`nIn = 3`; `I 0 = x`, `I 1 = y`, `I 2 = z`). The three-input
vector is `![x, y, z]`, so `inpGet ![x,y,z] 0 = x`, etc. -/

/-- The Maj source as a hax `ImpExpr`, fully let-normalized, parameters
    `["x","y","z"]`. Identical in shape to the `w = 32` `majSrc`. -/
def majSrc64 : ImpExpr :=
  .letBind "xy" (.app "BitAnd" [.var "x", .var "y"])
    (.letBind "xz" (.app "BitAnd" [.var "x", .var "z"])
      (.letBind "yz" (.app "BitAnd" [.var "y", .var "z"])
        (.letBind "t" (.app "BitXor" [.var "xy", .var "xz"])
          (.letBind "r" (.app "BitXor" [.var "t", .var "yz"])
            (.var "r")))))

/-- The Maj source denotes (under `denoteScalar`, parameters `["x","y","z"]`, at
    `w = 64`) to the FIPS formula `(x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)`, reading
    `x = inpGet I 0`, `y = inpGet I 1`, `z = inpGet I 2`. -/
theorem majSrc64_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar ["x", "y", "z"] I majSrc64 (fun _ => none)
      = some ((inpGet I 0 &&& inpGet I 1) ^^^ (inpGet I 0 &&& inpGet I 2)
                ^^^ (inpGet I 1 &&& inpGet I 2)) := by
  simp only [majSrc64, ImpExpr.denoteScalar, denoteAtomExpr, recogBin,
    List.idxOf?, List.findIdx?, JasminBinOp.apply,
    reduceIte, String.reduceEq]
  rfl

/-- The compile-from-hax pipeline succeeds on Maj (`w = 64`, three parameters). -/
theorem maj512_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 3) ["x", "y", "z"] majSrc64).isSome := by
  native_decide

/-- **SHA-512 Maj leaf emitted by the verified compiler (`w = 64`).** There is a
    compiled `Com jasminDialect` `c` with `compileFromHax ["x","y","z"] majSrc64 =
    some c`, and for every triple `(x, y, z)`, `c`'s `BitVec 64` denotation (under
    the input valuation `![x, y, z]`) is exactly the Maj formula
    `(x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)`. Routed through the C3 per-primitive obligation
    `compileFromHax_meets_spec`. -/
theorem maj512_compiles :
    ∃ (c : Com jasminDialect (frontCtxt 64 3 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 3) ["x", "y", "z"] majSrc64 = some c ∧
      ∀ (x y z : BitVec 64),
        c.denote (inputValuation 64 3 ![x, y, z])
          = (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z) := by
  set c := (compileFromHax (w := 64) (nIn := 3) ["x", "y", "z"] majSrc64).get
    maj512_compileFromHax_isSome with hc_def
  have hc : compileFromHax (w := 64) (nIn := 3) ["x", "y", "z"] majSrc64 = some c :=
    (Option.some_get _).symm
  refine ⟨c, hc, ?_⟩
  intro x y z
  -- The FIPS Maj source-spec at `![x, y, z]`: `inpGet ![x,y,z] i` reduces to the
  -- i-th component, so the spec is the plain `(x∧y) ⊕ (x∧z) ⊕ (y∧z)`.
  have hspec : ImpExpr.denoteScalar ["x", "y", "z"] ![x, y, z] majSrc64 (fun _ => none)
      = some ((x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)) := by
    have h := majSrc64_denoteScalar (nIn := 3) ![x, y, z]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using! h
  exact compileFromHax_meets_spec (w := 64) (nIn := 3) ["x", "y", "z"] ![x, y, z]
    majSrc64 _ hc hspec

/-! ## §2  Ch — the SHA-512 choose function (`w = 64`)

`Ch(x,y,z) = (x ∧ y) ⊕ (¬x ∧ z)`, at `w = 64`, three parameters `["x","y","z"]`
(`nIn = 3`; `I 0 = x`, `I 1 = y`, `I 2 = z`). The complement `¬x` is desugared at
the source as `BitXor[x, lit 18446744073709551615]` (the all-ones literal at
width 64), so the width-agnostic translator handles it via the existing `BitXor`
recogniser. -/

/-- The Ch source as a hax `ImpExpr`, fully let-normalized, parameters
    `["x","y","z"]`. The complement `¬x` is the desugared `BitXor[x, ones]` where
    `ones = 0xFFFFFFFFFFFFFFFF` is first bound to its own local (a bare-literal
    `Rhs.atom`, lowered to a `regConst`) — the front rejects a bare literal as a
    *binary-op operand* (`Atom.toVar (.lit _) = none`), so the all-ones constant
    must be materialized into a register first. -/
def chSrc64 : ImpExpr :=
  .letBind "ones" (.lit (.int 18446744073709551615))
    (.letBind "nx" (.app "BitXor" [.var "x", .var "ones"])
      (.letBind "t1" (.app "BitAnd" [.var "x", .var "y"])
        (.letBind "t2" (.app "BitAnd" [.var "nx", .var "z"])
          (.letBind "r" (.app "BitXor" [.var "t1", .var "t2"])
            (.var "r")))))

/-- The Ch source denotes (under `denoteScalar`, parameters `["x","y","z"]`, at
    `w = 64`) to the FIPS formula `(x ∧ y) ⊕ (¬x ∧ z)`, reading `x = inpGet I 0`,
    `y = inpGet I 1`, `z = inpGet I 2`. The desugared `x ^^^ 0xFFFFFFFFFFFFFFFF`
    collapses to `~~~x` via `BitVec.xor_allOnes`
    (`0xFFFFFFFFFFFFFFFF` denotes to `allOnes 64`). -/
theorem chSrc64_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar ["x", "y", "z"] I chSrc64 (fun _ => none)
      = some ((inpGet I 0 &&& inpGet I 1) ^^^ ((~~~ inpGet I 0) &&& inpGet I 2)) := by
  -- First reduce the let-chain (Maj-style) to the *un-rewritten* `x ^^^ ofNat …`
  -- form, then fold `ofNat 64 0xFFFFFFFFFFFFFFFF = allOnes` and `x ^^^ allOnes = ~~~x`.
  have e : ImpExpr.denoteScalar ["x", "y", "z"] I chSrc64 (fun _ => none)
      = some ((inpGet I 0 &&& inpGet I 1)
                ^^^ ((inpGet I 0 ^^^ BitVec.ofNat 64 18446744073709551615) &&& inpGet I 2)) := by
    simp only [chSrc64, ImpExpr.denoteScalar, denoteAtomExpr, recogBin,
      litNat?, JasminBinOp.apply, List.idxOf?, List.findIdx?,
      reduceIte, String.reduceEq, Int.toNat]
    rfl
  rw [e, show (BitVec.ofNat 64 18446744073709551615) = BitVec.allOnes 64 from by decide,
    BitVec.xor_allOnes]

/-- The compile-from-hax pipeline succeeds on Ch (`w = 64`, three parameters). -/
theorem ch512_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 3) ["x", "y", "z"] chSrc64).isSome := by
  native_decide

/-- **SHA-512 Ch leaf emitted by the verified compiler (`w = 64`).** There is a
    compiled `Com jasminDialect` `c` with `compileFromHax ["x","y","z"] chSrc64 =
    some c`, and for every triple `(x, y, z)`, `c`'s `BitVec 64` denotation (under
    the input valuation `![x, y, z]`) is exactly the Ch formula
    `(x ∧ y) ⊕ (¬x ∧ z)`. Routed through the C3 per-primitive obligation
    `compileFromHax_meets_spec`. -/
theorem ch512_compiles :
    ∃ (c : Com jasminDialect (frontCtxt 64 3 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 3) ["x", "y", "z"] chSrc64 = some c ∧
      ∀ (x y z : BitVec 64),
        c.denote (inputValuation 64 3 ![x, y, z])
          = (x &&& y) ^^^ ((~~~x) &&& z) := by
  set c := (compileFromHax (w := 64) (nIn := 3) ["x", "y", "z"] chSrc64).get
    ch512_compileFromHax_isSome with hc_def
  have hc : compileFromHax (w := 64) (nIn := 3) ["x", "y", "z"] chSrc64 = some c :=
    (Option.some_get _).symm
  refine ⟨c, hc, ?_⟩
  intro x y z
  -- The FIPS Ch source-spec at `![x, y, z]`: `inpGet ![x,y,z] i` reduces to the
  -- i-th component, so the spec is the plain `(x∧y) ⊕ (¬x∧z)`.
  have hspec : ImpExpr.denoteScalar ["x", "y", "z"] ![x, y, z] chSrc64 (fun _ => none)
      = some ((x &&& y) ^^^ ((~~~x) &&& z)) := by
    have h := chSrc64_denoteScalar (nIn := 3) ![x, y, z]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using! h
  exact compileFromHax_meets_spec (w := 64) (nIn := 3) ["x", "y", "z"] ![x, y, z]
    chSrc64 _ hc hspec

/-! ## §3  Σ₀ — the SHA-512 compression-function big sigma 0 (`w = 64`)

`Σ₀(x) = ROTR²⁸(x) ⊕ ROTR³⁴(x) ⊕ ROTR³⁹(x)`, at `w = 64`, one parameter `"x"`.
Same three-`rotate_right`/two-`BitXor` shape as the SHA-256 `bigSigma0Src`, only
with the SHA-512 rotation amounts (28, 34, 39). -/

/-- The Σ₀ source as a hax `ImpExpr`, fully let-normalized, parameter `"x"`. -/
def bigSigma0Src64 : ImpExpr :=
  .letBind "a" (.app "rotate_right" [.var "x", .lit (.int 28)])
    (.letBind "b" (.app "rotate_right" [.var "x", .lit (.int 34)])
      (.letBind "c" (.app "rotate_right" [.var "x", .lit (.int 39)])
        (.letBind "ab" (.app "BitXor" [.var "a", .var "b"])
          (.letBind "r" (.app "BitXor" [.var "ab", .var "c"])
            (.var "r")))))

/-- The Σ₀ source denotes (under `denoteScalar`, at `w = 64`) to the FIPS 180-4
    formula `ROTR²⁸(x) ⊕ ROTR³⁴(x) ⊕ ROTR³⁹(x)`. -/
theorem bigSigma0Src64_denoteScalar (I : Fin 1 → BitVec 64) :
    ImpExpr.denoteScalar ["x"] I bigSigma0Src64 (fun _ => none)
      = some ((I 0).rotateRight 28 ^^^ (I 0).rotateRight 34 ^^^ (I 0).rotateRight 39) := by
  simp only [bigSigma0Src64, ImpExpr.denoteScalar, denoteAtomExpr, recogBin, recogShift,
    litNat?, ShiftKind.apply, List.idxOf?, List.findIdx?, JasminBinOp.apply,
    reduceIte, String.reduceEq, Int.toNat]
  rfl

/-- The compile-from-hax pipeline succeeds on Σ₀ (`w = 64`, one parameter). -/
theorem bigSigma0_512_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 1) ["x"] bigSigma0Src64).isSome := by
  native_decide

/-- **SHA-512 Σ₀ leaf emitted by the verified compiler (`w = 64`).** There is a
    compiled `Com jasminDialect` `c` with `compileFromHax ["x"] bigSigma0Src64 =
    some c`, and for every input `x`, `c`'s `BitVec 64` denotation is exactly the
    FIPS 180-4 Σ₀ formula `(x ror 28) ⊕ (x ror 34) ⊕ (x ror 39)`. Routed through
    the C3 per-primitive obligation `compileFromHax_meets_spec`. -/
theorem bigSigma0_512_compiles :
    ∃ (c : Com jasminDialect (frontCtxt 64 1 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 1) ["x"] bigSigma0Src64 = some c ∧
      ∀ (x : BitVec 64),
        c.denote (inputValuation 64 1 (fun _ => x))
          = x.rotateRight 28 ^^^ x.rotateRight 34 ^^^ x.rotateRight 39 := by
  set c := (compileFromHax (w := 64) (nIn := 1) ["x"] bigSigma0Src64).get
    bigSigma0_512_compileFromHax_isSome with hc_def
  have hc : compileFromHax (w := 64) (nIn := 1) ["x"] bigSigma0Src64 = some c :=
    (Option.some_get _).symm
  refine ⟨c, hc, ?_⟩
  intro x
  have hspec := bigSigma0Src64_denoteScalar (fun _ => x)
  exact compileFromHax_meets_spec (w := 64) (nIn := 1) ["x"] (fun _ => x)
    bigSigma0Src64 _ hc hspec

/-! ## §4  Σ₁ — the SHA-512 compression-function big sigma 1 (`w = 64`)

`Σ₁(x) = ROTR¹⁴(x) ⊕ ROTR¹⁸(x) ⊕ ROTR⁴¹(x)`, at `w = 64`, one parameter `"x"`. -/

/-- The Σ₁ source as a hax `ImpExpr`, fully let-normalized, parameter `"x"`. -/
def bigSigma1Src64 : ImpExpr :=
  .letBind "a" (.app "rotate_right" [.var "x", .lit (.int 14)])
    (.letBind "b" (.app "rotate_right" [.var "x", .lit (.int 18)])
      (.letBind "c" (.app "rotate_right" [.var "x", .lit (.int 41)])
        (.letBind "ab" (.app "BitXor" [.var "a", .var "b"])
          (.letBind "r" (.app "BitXor" [.var "ab", .var "c"])
            (.var "r")))))

/-- The Σ₁ source denotes (under `denoteScalar`, at `w = 64`) to the FIPS 180-4
    formula `ROTR¹⁴(x) ⊕ ROTR¹⁸(x) ⊕ ROTR⁴¹(x)`. -/
theorem bigSigma1Src64_denoteScalar (I : Fin 1 → BitVec 64) :
    ImpExpr.denoteScalar ["x"] I bigSigma1Src64 (fun _ => none)
      = some ((I 0).rotateRight 14 ^^^ (I 0).rotateRight 18 ^^^ (I 0).rotateRight 41) := by
  simp only [bigSigma1Src64, ImpExpr.denoteScalar, denoteAtomExpr, recogBin, recogShift,
    litNat?, ShiftKind.apply, List.idxOf?, List.findIdx?, JasminBinOp.apply,
    reduceIte, String.reduceEq, Int.toNat]
  rfl

/-- The compile-from-hax pipeline succeeds on Σ₁ (`w = 64`, one parameter). -/
theorem bigSigma1_512_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 1) ["x"] bigSigma1Src64).isSome := by
  native_decide

/-- **SHA-512 Σ₁ leaf emitted by the verified compiler (`w = 64`).** There is a
    compiled `Com jasminDialect` `c` with `compileFromHax ["x"] bigSigma1Src64 =
    some c`, and for every input `x`, `c`'s `BitVec 64` denotation is exactly the
    FIPS 180-4 Σ₁ formula `(x ror 14) ⊕ (x ror 18) ⊕ (x ror 41)`. Routed through
    the C3 per-primitive obligation `compileFromHax_meets_spec`. -/
theorem bigSigma1_512_compiles :
    ∃ (c : Com jasminDialect (frontCtxt 64 1 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 1) ["x"] bigSigma1Src64 = some c ∧
      ∀ (x : BitVec 64),
        c.denote (inputValuation 64 1 (fun _ => x))
          = x.rotateRight 14 ^^^ x.rotateRight 18 ^^^ x.rotateRight 41 := by
  set c := (compileFromHax (w := 64) (nIn := 1) ["x"] bigSigma1Src64).get
    bigSigma1_512_compileFromHax_isSome with hc_def
  have hc : compileFromHax (w := 64) (nIn := 1) ["x"] bigSigma1Src64 = some c :=
    (Option.some_get _).symm
  refine ⟨c, hc, ?_⟩
  intro x
  have hspec := bigSigma1Src64_denoteScalar (fun _ => x)
  exact compileFromHax_meets_spec (w := 64) (nIn := 1) ["x"] (fun _ => x)
    bigSigma1Src64 _ hc hspec

/-! ## §5  σ₀ — the SHA-512 message-schedule small sigma 0 (`w = 64`)

`σ₀(x) = ROTR¹(x) ⊕ ROTR⁸(x) ⊕ SHR⁷(x)`, at `w = 64`, one parameter `"x"`. The
third term is a logical *shift* (`shift_right`), not a rotate; it lowers via the
`shr` recogniser and denotes to `x >>> 7`. -/

/-- The σ₀ source as a hax `ImpExpr`, fully let-normalized, parameter `"x"`. -/
def sigma0Src64 : ImpExpr :=
  .letBind "a" (.app "rotate_right" [.var "x", .lit (.int 1)])
    (.letBind "b" (.app "rotate_right" [.var "x", .lit (.int 8)])
      (.letBind "c" (.app "shift_right" [.var "x", .lit (.int 7)])
        (.letBind "ab" (.app "BitXor" [.var "a", .var "b"])
          (.letBind "r" (.app "BitXor" [.var "ab", .var "c"])
            (.var "r")))))

/-- The σ₀ source denotes (under `denoteScalar`, at `w = 64`) to the FIPS 180-4
    formula `ROTR¹(x) ⊕ ROTR⁸(x) ⊕ SHR⁷(x)`. -/
theorem sigma0Src64_denoteScalar (I : Fin 1 → BitVec 64) :
    ImpExpr.denoteScalar ["x"] I sigma0Src64 (fun _ => none)
      = some ((I 0).rotateRight 1 ^^^ (I 0).rotateRight 8 ^^^ (I 0) >>> (7 : Nat)) := by
  simp only [sigma0Src64, ImpExpr.denoteScalar, denoteAtomExpr, recogBin, recogShift,
    litNat?, ShiftKind.apply, List.idxOf?, List.findIdx?, JasminBinOp.apply,
    reduceIte, String.reduceEq, Int.toNat]
  rfl

/-- The compile-from-hax pipeline succeeds on σ₀ (`w = 64`, one parameter). -/
theorem sigma0_512_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 1) ["x"] sigma0Src64).isSome := by
  native_decide

/-- **SHA-512 σ₀ leaf emitted by the verified compiler (`w = 64`).** There is a
    compiled `Com jasminDialect` `c` with `compileFromHax ["x"] sigma0Src64 =
    some c`, and for every input `x`, `c`'s `BitVec 64` denotation is exactly the
    FIPS 180-4 σ₀ formula `(x ror 1) ⊕ (x ror 8) ⊕ (x >> 7)`. Routed through the
    C3 per-primitive obligation `compileFromHax_meets_spec`. -/
theorem sigma0_512_compiles :
    ∃ (c : Com jasminDialect (frontCtxt 64 1 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 1) ["x"] sigma0Src64 = some c ∧
      ∀ (x : BitVec 64),
        c.denote (inputValuation 64 1 (fun _ => x))
          = x.rotateRight 1 ^^^ x.rotateRight 8 ^^^ x >>> (7 : Nat) := by
  set c := (compileFromHax (w := 64) (nIn := 1) ["x"] sigma0Src64).get
    sigma0_512_compileFromHax_isSome with hc_def
  have hc : compileFromHax (w := 64) (nIn := 1) ["x"] sigma0Src64 = some c :=
    (Option.some_get _).symm
  refine ⟨c, hc, ?_⟩
  intro x
  have hspec := sigma0Src64_denoteScalar (fun _ => x)
  exact compileFromHax_meets_spec (w := 64) (nIn := 1) ["x"] (fun _ => x)
    sigma0Src64 _ hc hspec

/-! ## §6  σ₁ — the SHA-512 message-schedule small sigma 1 (`w = 64`)

`σ₁(x) = ROTR¹⁹(x) ⊕ ROTR⁶¹(x) ⊕ SHR⁶(x)`, at `w = 64`, one parameter `"x"`. -/

/-- The σ₁ source as a hax `ImpExpr`, fully let-normalized, parameter `"x"`. -/
def sigma1Src64 : ImpExpr :=
  .letBind "a" (.app "rotate_right" [.var "x", .lit (.int 19)])
    (.letBind "b" (.app "rotate_right" [.var "x", .lit (.int 61)])
      (.letBind "c" (.app "shift_right" [.var "x", .lit (.int 6)])
        (.letBind "ab" (.app "BitXor" [.var "a", .var "b"])
          (.letBind "r" (.app "BitXor" [.var "ab", .var "c"])
            (.var "r")))))

/-- The σ₁ source denotes (under `denoteScalar`, at `w = 64`) to the FIPS 180-4
    formula `ROTR¹⁹(x) ⊕ ROTR⁶¹(x) ⊕ SHR⁶(x)`. -/
theorem sigma1Src64_denoteScalar (I : Fin 1 → BitVec 64) :
    ImpExpr.denoteScalar ["x"] I sigma1Src64 (fun _ => none)
      = some ((I 0).rotateRight 19 ^^^ (I 0).rotateRight 61 ^^^ (I 0) >>> (6 : Nat)) := by
  simp only [sigma1Src64, ImpExpr.denoteScalar, denoteAtomExpr, recogBin, recogShift,
    litNat?, ShiftKind.apply, List.idxOf?, List.findIdx?, JasminBinOp.apply,
    reduceIte, String.reduceEq, Int.toNat]
  rfl

/-- The compile-from-hax pipeline succeeds on σ₁ (`w = 64`, one parameter). -/
theorem sigma1_512_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 1) ["x"] sigma1Src64).isSome := by
  native_decide

/-- **SHA-512 σ₁ leaf emitted by the verified compiler (`w = 64`).** There is a
    compiled `Com jasminDialect` `c` with `compileFromHax ["x"] sigma1Src64 =
    some c`, and for every input `x`, `c`'s `BitVec 64` denotation is exactly the
    FIPS 180-4 σ₁ formula `(x ror 19) ⊕ (x ror 61) ⊕ (x >> 6)`. Routed through the
    C3 per-primitive obligation `compileFromHax_meets_spec`. -/
theorem sigma1_512_compiles :
    ∃ (c : Com jasminDialect (frontCtxt 64 1 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 1) ["x"] sigma1Src64 = some c ∧
      ∀ (x : BitVec 64),
        c.denote (inputValuation 64 1 (fun _ => x))
          = x.rotateRight 19 ^^^ x.rotateRight 61 ^^^ x >>> (6 : Nat) := by
  set c := (compileFromHax (w := 64) (nIn := 1) ["x"] sigma1Src64).get
    sigma1_512_compileFromHax_isSome with hc_def
  have hc : compileFromHax (w := 64) (nIn := 1) ["x"] sigma1Src64 = some c :=
    (Option.some_get _).symm
  refine ⟨c, hc, ?_⟩
  intro x
  have hspec := sigma1Src64_denoteScalar (fun _ => x)
  exact compileFromHax_meets_spec (w := 64) (nIn := 1) ["x"] (fun _ => x)
    sigma1Src64 _ hc hspec

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxSha512
