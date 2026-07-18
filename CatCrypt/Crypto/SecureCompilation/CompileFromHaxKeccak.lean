/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHax

/-!
# C4 fan-out: the verified compiler emits a Keccak χ leaf from extracted source

This module extends the **C4** step of the verified-compiler plan to a **second
primitive family**: Keccak. The C4 SHA-256 leaves (`CompileFromHaxLeaves`)
showed `compileFromHax` *emitting* the SHA-256 round components from
hax-extracted source. Here we do the same for the Keccak-f[1600] non-linear
step **χ (chi)** — the only non-linear map in the Keccak permutation.

χ uses *only* bitwise `Not`/`And`/`Xor` — no rotate, no shift — so it reuses the
exactly the recognizer chain already exercised by the SHA-256 `Ch` leaf
(`CompileFromHaxLeaves.ch_compiles`). **No change to the verified front is
required**; this is a clean fan-out data point to a new primitive family.

## Keccak χ (FIPS 202)

For a 5-lane row `a[0..4]` (each lane a `BitVec w`), χ outputs

```
b[x] = a[x] ^ ((¬a[x+1]) & a[x+2])     (indices mod 5)
```

This file emits **one output lane** `b = a0 ^ ((¬a1) & a2)`, the canonical χ
shape, with the three relevant input lanes `a0 = a[x]`, `a1 = a[x+1]`,
`a2 = a[x+2]` as the three parameters (`nIn = 3`). The full χ permutation is
**25 lanes** (5 rows × 5 positions), each exactly this `^/¬/&` shape over a
rotation of the row — so the single-lane mechanism scales by replication.

## Method (mirrors `CompileFromHaxLeaves.ch_compiles`)

`Ch(x,y,z) = (x ∧ y) ⊕ (¬x ∧ z)` and the χ lane `b = a0 ⊕ ((¬a1) ∧ a2)` are the
same `Not`/`And`/`Xor` family. As in `ch_compiles`, the complement `¬a1` is
**desugared** at the source as `BitXor[a1, lit (2³²−1)]` (the all-ones literal at
width 32, `2³²−1 = 4294967295`), since the width-agnostic translator (`rhsOf`)
cannot synthesise the all-ones literal but the existing `BitXor` recogniser
handles the desugared form. `BitVec.xor_allOnes` folds `a1 ⊕ allOnes` back to
`~~~a1` in the source-spec lemma. The all-ones constant is first bound to its
own local (`ones`) so it is materialised into a register before use as a binary
operand (a bare literal is rejected as a binary-op operand by the front).

The lane then follows the C3 obligation pattern exactly:

1. `chiLaneSrc` — a let-normalized `ImpExpr` source.
2. `chiLaneSrc_denoteScalar` — the source `denoteScalar` computes the χ formula
   (the `^^^ allOnes` collapses to `~~~` via `BitVec.xor_allOnes`).
3. `chiLane_compileFromHax_isSome` — the compile succeeds (`native_decide`).
4. `chiLane_compiles` — the emitted jasmin `Com` denotes to `a0 ⊕ ((¬a1) ∧ a2)`,
   routed through the C3 per-primitive obligation `compileFromHax_meets_spec`.

The emitted jasmin `Com` is *computed by the verified compiler from the extracted
source*, proven equal to the FIPS 202 χ-lane formula — the compiler authored the
leaf, with no front change beyond the SHA-256 `Ch` leaf.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxKeccak

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## A single Keccak χ output lane

`b = a0 ⊕ ((¬a1) ∧ a2)`, at `w = 32`, three parameters `["a0","a1","a2"]`
(`nIn = 3`; `I 0 = a0`, `I 1 = a1`, `I 2 = a2`). The three-input vector is
`![a0, a1, a2]`, so `inpGet ![a0,a1,a2] 0 = a0`, etc. The complement `¬a1` is
desugared at the source as `BitXor[a1, lit 4294967295]` (the all-ones literal at
width 32), exactly as in `CompileFromHaxLeaves.chSrc`. -/

/-- The Keccak χ-lane source as a hax `ImpExpr`, fully let-normalized, parameters
    `["a0","a1","a2"]`. The complement `¬a1` is the desugared `BitXor[a1, ones]`
    where `ones = 0xFFFFFFFF` is first bound to its own local (a bare-literal
    `Rhs.atom`, lowered to a `regConst`) — the front rejects a bare literal as a
    *binary-op operand*, so the all-ones constant must be materialized into a
    register first. The v1 binary-ALU translator then accepts every op. -/
def chiLaneSrc : ImpExpr :=
  .letBind "ones" (.lit (.int 4294967295))
    (.letBind "na1" (.app "BitXor" [.var "a1", .var "ones"])
      (.letBind "t" (.app "BitAnd" [.var "na1", .var "a2"])
        (.letBind "r" (.app "BitXor" [.var "a0", .var "t"])
          (.var "r"))))

/-- The χ-lane source denotes (under `denoteScalar`, parameters `["a0","a1","a2"]`)
    to the FIPS 202 χ formula `a0 ⊕ ((¬a1) ∧ a2)`, reading `a0 = inpGet I 0`,
    `a1 = inpGet I 1`, `a2 = inpGet I 2`. The desugared `a1 ^^^ 0xFFFFFFFF`
    collapses to `~~~a1` via `BitVec.xor_allOnes` (`0xFFFFFFFF` denotes to
    `allOnes 32`). -/
theorem chiLaneSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 32) :
    ImpExpr.denoteScalar ["a0", "a1", "a2"] I chiLaneSrc (fun _ => none)
      = some (inpGet I 0 ^^^ ((~~~ inpGet I 1) &&& inpGet I 2)) := by
  -- First reduce the let-chain (Ch-style) to the *un-rewritten* `a1 ^^^ ofNat …`
  -- form, then fold `ofNat 32 0xFFFFFFFF = allOnes` and `a1 ^^^ allOnes = ~~~a1`.
  have e : ImpExpr.denoteScalar ["a0", "a1", "a2"] I chiLaneSrc (fun _ => none)
      = some (inpGet I 0
                ^^^ ((inpGet I 1 ^^^ BitVec.ofNat 32 4294967295) &&& inpGet I 2)) := by
    simp only [chiLaneSrc, ImpExpr.denoteScalar, denoteAtomExpr, recogBin,
      litNat?, JasminBinOp.apply, List.idxOf?, List.findIdx?,
      reduceIte, String.reduceEq, Int.toNat]
    rfl
  rw [e, show (BitVec.ofNat 32 4294967295) = BitVec.allOnes 32 from by decide,
    BitVec.xor_allOnes]

/-- The compile-from-hax pipeline succeeds on the χ lane (`w = 32`, three
    parameters). -/
theorem chiLane_compileFromHax_isSome :
    (compileFromHax (w := 32) (nIn := 3) ["a0", "a1", "a2"] chiLaneSrc).isSome := by
  native_decide

/-- **Keccak χ lane emitted by the verified compiler.** There is a compiled
    `Com jasminDialect` `c` with `compileFromHax ["a0","a1","a2"] chiLaneSrc = some c`,
    and for every triple `(a0, a1, a2)`, `c`'s `BitVec 32` denotation (under the
    input valuation `![a0, a1, a2]`) is exactly the FIPS 202 χ-lane formula
    `a0 ⊕ ((¬a1) ∧ a2)`. Routed through the C3 per-primitive obligation
    `compileFromHax_meets_spec`. This is a C4 fan-out to a *second* primitive
    family (Keccak), reusing the SHA-256 `Ch` leaf's `Not`/`And`/`Xor` recognizer
    chain with no front change. The full χ permutation is 25 lanes of exactly this
    shape. -/
theorem chiLane_compiles :
    ∃ (c : Com jasminDialect (frontCtxt 32 3 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 3) ["a0", "a1", "a2"] chiLaneSrc = some c ∧
      ∀ (a0 a1 a2 : BitVec 32),
        c.denote (inputValuation 32 3 ![a0, a1, a2])
          = a0 ^^^ ((~~~a1) &&& a2) := by
  set c := (compileFromHax (w := 32) (nIn := 3) ["a0", "a1", "a2"] chiLaneSrc).get
    chiLane_compileFromHax_isSome with hc_def
  have hc : compileFromHax (w := 32) (nIn := 3) ["a0", "a1", "a2"] chiLaneSrc = some c :=
    (Option.some_get _).symm
  refine ⟨c, hc, ?_⟩
  intro a0 a1 a2
  -- The FIPS χ-lane source-spec at `![a0, a1, a2]`: `inpGet ![a0,a1,a2] i` reduces
  -- to the i-th component, so the spec is the plain `a0 ⊕ ((¬a1) ∧ a2)`.
  have hspec : ImpExpr.denoteScalar ["a0", "a1", "a2"] ![a0, a1, a2] chiLaneSrc (fun _ => none)
      = some (a0 ^^^ ((~~~a1) &&& a2)) := by
    have h := chiLaneSrc_denoteScalar (nIn := 3) ![a0, a1, a2]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using h
  exact compileFromHax_meets_spec (w := 32) (nIn := 3) ["a0", "a1", "a2"] ![a0, a1, a2]
    chiLaneSrc _ hc hspec

/-! ## The Keccak ι (iota) step — round-constant XOR on lane (0,0)

FIPS 202 §3.2.5: `A'[0,0] = A[0,0] ⊕ RC`. We model the single affected lane as a
one-parameter (`nIn = 1`, parameter `["a"]`) leaf at `w = 64`, with the round
constant `RC` taken as the **fixed literal** `RC₀ = 0x0000000000000001` (the
first FIPS 202 round constant; `keccak_round_constant 0 = 1`). The constant is
first bound to its own local (`rc`, a bare-literal `Rhs.atom`, lowered to a
`regConst`) — the front rejects a bare literal as a *binary-op operand*, so the
round constant must be materialized into a register first, exactly as the χ-lane
all-ones constant is. The leaf then XORs it into the input lane:
`r = a ⊕ rc`, denoting to `a ⊕ (1 : BitVec 64)`.

This mirrors `chiLane_compiles` arm-for-arm (let-normalized `*Src` → `*_denoteScalar`
→ `*_compileFromHax_isSome` (`native_decide`) → `*_compiles` via
`compileFromHax_meets_spec`), at `w = 64` and `nIn = 1`. -/

/-- The Keccak ι-lane source as a hax `ImpExpr`, parameter `["a"]`. `RC₀ = 1` is
    first bound to its own local `rc` (a bare-literal `Rhs.atom`, lowered to a
    `regConst`) — the front rejects a bare literal as a *binary-op operand*, so
    the round constant must be materialized into a register first. The single
    `BitXor[a, rc]` is the round-constant XOR `A'[0,0] = A[0,0] ⊕ RC`. -/
def iotaSrc : ImpExpr :=
  .letBind "rc" (.lit (.int 1))
    (.letBind "r" (.app "BitXor" [.var "a", .var "rc"])
      (.var "r"))

/-- The ι-lane source denotes (under `denoteScalar`, parameter `["a"]`) to the
    FIPS 202 ι formula `A[0,0] ⊕ RC₀` with `RC₀ = (1 : BitVec 64)`, reading
    `a = inpGet I 0`. -/
theorem iotaSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar ["a"] I iotaSrc (fun _ => none)
      = some (inpGet I 0 ^^^ (1 : BitVec 64)) := by
  simp only [iotaSrc, ImpExpr.denoteScalar, denoteAtomExpr, recogBin,
    litNat?, JasminBinOp.apply, List.idxOf?, List.findIdx?,
    reduceIte, String.reduceEq, Int.toNat]
  rfl

/-- The compile-from-hax pipeline succeeds on the ι lane (`w = 64`, one
    parameter). -/
theorem iotaLane_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 1) ["a"] iotaSrc).isSome := by
  native_decide

/-- **Keccak ι lane emitted by the verified compiler.** There is a compiled
    `Com jasminDialect` `c` with `compileFromHax ["a"] iotaSrc = some c`, and for
    every input lane `a`, `c`'s `BitVec 64` denotation (under the input valuation
    `![a]`) is exactly the FIPS 202 ι-lane formula `a ⊕ RC₀` with `RC₀ = 1`.
    Routed through the C3 per-primitive obligation `compileFromHax_meets_spec`.
    The full ι step touches only lane (0,0) per round; the per-round constant
    varies (`keccak_round_constant round`) but the leaf shape is this single XOR. -/
theorem iotaLane_compiles :
    ∃ (c : Com jasminDialect (frontCtxt 64 1 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 1) ["a"] iotaSrc = some c ∧
      ∀ (a : BitVec 64),
        c.denote (inputValuation 64 1 ![a])
          = a ^^^ (1 : BitVec 64) := by
  set c := (compileFromHax (w := 64) (nIn := 1) ["a"] iotaSrc).get
    iotaLane_compileFromHax_isSome with hc_def
  have hc : compileFromHax (w := 64) (nIn := 1) ["a"] iotaSrc = some c :=
    (Option.some_get _).symm
  refine ⟨c, hc, ?_⟩
  intro a
  have hspec : ImpExpr.denoteScalar ["a"] ![a] iotaSrc (fun _ => none)
      = some (a ^^^ (1 : BitVec 64)) := by
    have h := iotaSrc_denoteScalar (nIn := 1) ![a]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.cons_val] using h
  exact compileFromHax_meets_spec (w := 64) (nIn := 1) ["a"] ![a]
    iotaSrc _ hc hspec

/-! ## The Keccak θ diffusion lane (θ-D) — the ARX core of θ

FIPS 202 §3.2.1: after the column parities `C[x] = ⊕_y A[x,y]`, the diffusion
lanes are `D[x] = C[x-1] ⊕ rotl64(C[x+1], 1)`. We model the ARX core with the
two column-parities `C[x-1] = c0` and `C[x+1] = c1` as the two leaf inputs
(`nIn = 2`, parameters `["c0","c1"]`, `w = 64`), computing
`D = c0 ⊕ rotl64(c1, 1)`.

The `rotate_right` recognizer (`recogShift`, head `rotate_right` → `Rhs.ror n`,
denoting to `rotateRight n`) is the only rotate the front exposes; on width 64,
`rotl64(c1, 1) = c1.rotateRight 63` (a left-rotate by 1 = a right-rotate by
`64 − 1 = 63`). So the source uses `rotate_right[c1, 63]` and the spec is stated
in the `rotateRight 63` form the op denotes to. -/

/-- The Keccak θ-D source as a hax `ImpExpr`, parameters `["c0","c1"]`. The
    `rotl64(c1, 1)` of FIPS 202 is the width-64 identity `c1.rotateRight 63`
    (left-rotate by 1 = right-rotate by 63), emitted via the `rotate_right`
    recognizer (`Rhs.ror 63`). The diffusion XOR `D = c0 ⊕ rotl64(c1,1)` is the
    final `BitXor`. -/
def thetaDSrc : ImpExpr :=
  .letBind "t" (.app "rotate_right" [.var "c1", .lit (.int 63)])
    (.letBind "r" (.app "BitXor" [.var "c0", .var "t"])
      (.var "r"))

/-- The θ-D source denotes (under `denoteScalar`, parameters `["c0","c1"]`) to the
    FIPS 202 diffusion lane `D = c0 ⊕ rotl64(c1, 1)`, with `rotl64(c1,1)` written
    as the width-64 equivalent `c1.rotateRight 63`. Reads `c0 = inpGet I 0`,
    `c1 = inpGet I 1`. -/
theorem thetaDSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar ["c0", "c1"] I thetaDSrc (fun _ => none)
      = some (inpGet I 0 ^^^ (inpGet I 1).rotateRight 63) := by
  simp only [thetaDSrc, ImpExpr.denoteScalar, denoteAtomExpr, recogBin,
    recogShift, litNat?, ShiftKind.apply, JasminBinOp.apply,
    List.idxOf?, List.findIdx?, reduceIte, String.reduceEq, Int.toNat]
  rfl

/-- The compile-from-hax pipeline succeeds on the θ-D lane (`w = 64`, two
    parameters). -/
theorem thetaDLane_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 2) ["c0", "c1"] thetaDSrc).isSome := by
  native_decide

/-- **Keccak θ-D lane emitted by the verified compiler.** There is a compiled
    `Com jasminDialect` `c` with `compileFromHax ["c0","c1"] thetaDSrc = some c`,
    and for every column-parity pair `(c0, c1)`, `c`'s `BitVec 64` denotation
    (under the input valuation `![c0, c1]`) is exactly the FIPS 202 θ diffusion
    lane `c0 ⊕ rotl64(c1, 1)`, written in the width-64 `rotateRight 63` form.
    Routed through the C3 per-primitive obligation `compileFromHax_meets_spec`.
    This is the ARX core of θ; the 5-lane column parity `C[x]` is `thetaCLane`
    below. -/
theorem thetaDLane_compiles :
    ∃ (c : Com jasminDialect (frontCtxt 64 2 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 2) ["c0", "c1"] thetaDSrc = some c ∧
      ∀ (c0 c1 : BitVec 64),
        c.denote (inputValuation 64 2 ![c0, c1])
          = c0 ^^^ c1.rotateRight 63 := by
  set c := (compileFromHax (w := 64) (nIn := 2) ["c0", "c1"] thetaDSrc).get
    thetaDLane_compileFromHax_isSome with hc_def
  have hc : compileFromHax (w := 64) (nIn := 2) ["c0", "c1"] thetaDSrc = some c :=
    (Option.some_get _).symm
  refine ⟨c, hc, ?_⟩
  intro c0 c1
  have hspec : ImpExpr.denoteScalar ["c0", "c1"] ![c0, c1] thetaDSrc (fun _ => none)
      = some (c0 ^^^ c1.rotateRight 63) := by
    have h := thetaDSrc_denoteScalar (nIn := 2) ![c0, c1]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using h
  exact compileFromHax_meets_spec (w := 64) (nIn := 2) ["c0", "c1"] ![c0, c1]
    thetaDSrc _ hc hspec

/-! ## The Keccak θ column parity (θ-C) — the 5-lane column XOR

FIPS 202 §3.2.1: `C[x] = A[x,0] ⊕ A[x,1] ⊕ A[x,2] ⊕ A[x,3] ⊕ A[x,4]`. A pure
chained-XOR reduction over the five lanes of a column (`nIn = 5`, parameters
`["a0","a1","a2","a3","a4"]`, `w = 64`), feeding the `c0`/`c1` inputs of the
θ-D leaf above. -/

/-- The Keccak θ-C source as a hax `ImpExpr`, parameters `["a0".."a4"]`. The
    column parity `C[x] = a0 ⊕ a1 ⊕ a2 ⊕ a3 ⊕ a4` as a left-nested `BitXor`
    chain. -/
def thetaCSrc : ImpExpr :=
  .letBind "t1" (.app "BitXor" [.var "a0", .var "a1"])
    (.letBind "t2" (.app "BitXor" [.var "t1", .var "a2"])
      (.letBind "t3" (.app "BitXor" [.var "t2", .var "a3"])
        (.letBind "r" (.app "BitXor" [.var "t3", .var "a4"])
          (.var "r"))))

/-- The θ-C source denotes (under `denoteScalar`, parameters `["a0".."a4"]`) to the
    FIPS 202 column parity `C = a0 ⊕ a1 ⊕ a2 ⊕ a3 ⊕ a4`, reading
    `ai = inpGet I i`. -/
theorem thetaCSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar ["a0", "a1", "a2", "a3", "a4"] I thetaCSrc (fun _ => none)
      = some (inpGet I 0 ^^^ inpGet I 1 ^^^ inpGet I 2 ^^^ inpGet I 3 ^^^ inpGet I 4) := by
  simp only [thetaCSrc, ImpExpr.denoteScalar, denoteAtomExpr, recogBin,
    JasminBinOp.apply, List.idxOf?, List.findIdx?,
    reduceIte, String.reduceEq]
  rfl

/-- The compile-from-hax pipeline succeeds on the θ-C column parity (`w = 64`,
    five parameters). -/
theorem thetaCLane_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 5) ["a0", "a1", "a2", "a3", "a4"] thetaCSrc).isSome := by
  native_decide

/-- **Keccak θ-C column parity emitted by the verified compiler.** There is a
    compiled `Com jasminDialect` `c` with
    `compileFromHax ["a0".."a4"] thetaCSrc = some c`, and for every column
    `(a0, a1, a2, a3, a4)`, `c`'s `BitVec 64` denotation (under `![a0,…,a4]`) is
    exactly the FIPS 202 column parity `a0 ⊕ a1 ⊕ a2 ⊕ a3 ⊕ a4`. Routed through
    `compileFromHax_meets_spec`. Feeds the `c0`/`c1` inputs of `thetaDLane`. -/
theorem thetaCLane_compiles :
    ∃ (c : Com jasminDialect (frontCtxt 64 5 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 5) ["a0", "a1", "a2", "a3", "a4"] thetaCSrc = some c ∧
      ∀ (a0 a1 a2 a3 a4 : BitVec 64),
        c.denote (inputValuation 64 5 ![a0, a1, a2, a3, a4])
          = a0 ^^^ a1 ^^^ a2 ^^^ a3 ^^^ a4 := by
  set c := (compileFromHax (w := 64) (nIn := 5) ["a0", "a1", "a2", "a3", "a4"] thetaCSrc).get
    thetaCLane_compileFromHax_isSome with hc_def
  have hc : compileFromHax (w := 64) (nIn := 5) ["a0", "a1", "a2", "a3", "a4"] thetaCSrc = some c :=
    (Option.some_get _).symm
  refine ⟨c, hc, ?_⟩
  intro a0 a1 a2 a3 a4
  have hspec : ImpExpr.denoteScalar ["a0", "a1", "a2", "a3", "a4"] ![a0, a1, a2, a3, a4]
      thetaCSrc (fun _ => none)
      = some (a0 ^^^ a1 ^^^ a2 ^^^ a3 ^^^ a4) := by
    have h := thetaCSrc_denoteScalar (nIn := 5) ![a0, a1, a2, a3, a4]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using h
  exact compileFromHax_meets_spec (w := 64) (nIn := 5) ["a0", "a1", "a2", "a3", "a4"]
    ![a0, a1, a2, a3, a4] thetaCSrc _ hc hspec

/-! ## The Keccak ρ (rho) lane rotation — a representative lane rotate

FIPS 202 §3.2.2: `A'[x,y] = rotl64(A[x,y], rotOffset(x,y))`. Each lane is rotated
left by its fixed rotation offset (`Primitives.Keccak.rotOffset`). We model **one
representative lane**, lane `(0,1)`, whose offset is `36` (`rotData[0][1] = 36`),
as a one-parameter (`nIn = 1`, parameter `["a"]`) leaf at `w = 64`.

The `rotate_right` recognizer is the only rotate the front exposes; on width 64 a
left-rotate by `36` is the identity `rotl64(a, 36) = a.rotateRight (64 − 36) =
a.rotateRight 28`. So the source uses `rotate_right[a, 28]` and the spec is stated
in the `rotateRight 28` form the op denotes to. The other 24 lanes are exactly
this single-rotate shape at their own offset (`rotOffset x y`); the mechanism
scales by replication with a per-lane literal count. -/

/-- The Keccak ρ-lane source as a hax `ImpExpr`, parameter `["a"]`. Lane `(0,1)`
    has rotation offset `36`; the FIPS `rotl64(a, 36)` is the width-64 identity
    `a.rotateRight 28` (left-rotate by 36 = right-rotate by `64 − 36 = 28`),
    emitted via the `rotate_right` recognizer (`Rhs.ror 28`). -/
def rhoLaneSrc : ImpExpr :=
  .letBind "r" (.app "rotate_right" [.var "a", .lit (.int 28)])
    (.var "r")

/-- The ρ-lane source denotes (under `denoteScalar`, parameter `["a"]`) to the
    FIPS 202 lane rotation `A'[0,1] = rotl64(a, 36)`, with `rotl64(a, 36)` written
    as the width-64 equivalent `a.rotateRight 28`. Reads `a = inpGet I 0`. -/
theorem rhoLaneSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar ["a"] I rhoLaneSrc (fun _ => none)
      = some ((inpGet I 0).rotateRight 28) := by
  simp only [rhoLaneSrc, ImpExpr.denoteScalar, denoteAtomExpr, recogBin,
    recogShift, litNat?, ShiftKind.apply, JasminBinOp.apply,
    List.idxOf?, List.findIdx?, reduceIte, String.reduceEq, Int.toNat]
  rfl

/-- The compile-from-hax pipeline succeeds on the ρ lane (`w = 64`, one
    parameter). -/
theorem rhoLane_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 1) ["a"] rhoLaneSrc).isSome := by
  native_decide

/-- **Keccak ρ lane emitted by the verified compiler.** There is a compiled
    `Com jasminDialect` `c` with `compileFromHax ["a"] rhoLaneSrc = some c`, and
    for every input lane `a`, `c`'s `BitVec 64` denotation (under the input
    valuation `![a]`) is exactly the FIPS 202 ρ lane rotation for lane `(0,1)`,
    written in the width-64 `rotateRight 28` form (= `rotl64(a, 36)`). Routed
    through the C3 per-primitive obligation `compileFromHax_meets_spec`. The full
    ρ step rotates each of the 25 lanes by its own `rotOffset`; the per-lane
    rotate count varies but the leaf shape is this single `rotate_right`. -/
theorem rhoLane_compiles :
    ∃ (c : Com jasminDialect (frontCtxt 64 1 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 1) ["a"] rhoLaneSrc = some c ∧
      ∀ (a : BitVec 64),
        c.denote (inputValuation 64 1 ![a])
          = a.rotateRight 28 := by
  set c := (compileFromHax (w := 64) (nIn := 1) ["a"] rhoLaneSrc).get
    rhoLane_compileFromHax_isSome with hc_def
  have hc : compileFromHax (w := 64) (nIn := 1) ["a"] rhoLaneSrc = some c :=
    (Option.some_get _).symm
  refine ⟨c, hc, ?_⟩
  intro a
  have hspec : ImpExpr.denoteScalar ["a"] ![a] rhoLaneSrc (fun _ => none)
      = some (a.rotateRight 28) := by
    have h := rhoLaneSrc_denoteScalar (nIn := 1) ![a]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.cons_val] using h
  exact compileFromHax_meets_spec (w := 64) (nIn := 1) ["a"] ![a]
    rhoLaneSrc _ hc hspec

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxKeccak
