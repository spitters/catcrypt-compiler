/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.CompileFromHax
public import CatCrypt.Crypto.SecureCompilation.CompileFromHax

/-!
# C4 hash-composition fan-out: the SLH-DSA WOTS+ chain-step SHA-256 inner-round combiner

This module is the **hash-composition** Category-C leaf for the verified-compiler
plan — the shape after the arithmetic-MAC lattice leaves
(`CompileFromHaxFrodoMac` / `CompileFromHaxNtruMul` / `CompileFromHaxSntrupMul`).
Where those compose a single ring/field reduce, this leaf **composes two SHA-256
round components** (`Σ₀` and `Maj`) through an integer add — exactly the
combiner that drives the SHA-256 round transformation at the heart of the
SLH-DSA WOTS+ hash chain step `F` (the `sha2-*` parameter sets, FIPS 205 §10.2 /
§11.2).

## What this is — and the hash-composition shape

SLH-DSA (FIPS 205) is the stateless hash-based signature whose hypertree of
WOTS+ / FORS / Merkle levels is parameterised over a tweakable hash family. For
the `sha2-128{s,f}` / `sha2-192{s,f}` / `sha2-256{s,f}` parameter sets, the
WOTS+ chain step `F(PK.seed, ADRS, M)` is a SHA-256 call, whose engine is the
FIPS 180-4 §6.2 single round transformation `sha256RoundVerified`. That round's
working-variable update binds two local quantities:

```text
   T1 = h + Σ₁(e) + Ch(e,f,g) + K[t] + W[t]
   T2 = Σ₀(a) + Maj(a,b,c)
   a' = T1 + T2     b' = a    ...    e' = d + T1   ...
```

`T2 = Σ₀(a) + Maj(a,b,c)` is the **purely state-driven** half of the round —
the part that depends only on the chaining-state words `(a,b,c)`, with no
round constant or schedule word. It is the cleanest hash-composition tie: a
single straight-line leaf that

* rotates+XORs three copies of `a` (the `Σ₀` round component), and
* ANDs+XORs the three words `(a,b,c)` (the `Maj` round component), and
* **adds** the two together.

The `Σ₀` and `Maj` sub-expressions are *exactly* the already-tied SHA-256
round-component leaves (`CompileFromHaxLeaves.{bigSigma0,maj}_compiles`,
transported onto `Sha256Verified.{bigSigma0,maj}` in `CompileFromHaxSha2KeccakTie`).
So this leaf composes the tied SHA-256 components — it does **not** re-prove
`Σ₀`/`Maj`; the companion tie reuses them and the round's reference engine
`Sha256Verified.sha256RoundVerified` directly.

## Honest framing

This is a **functional-equality** leaf, not a security claim. SLH-DSA's hash
chain is built on SHA-256, an unkeyed compression primitive; nothing here
establishes preimage/collision resistance or the WOTS+/FORS EUF-CMA reduction
(those live in `SLHDSA/Reduction.lean` over the abstract `TweakableHashParams`).
The result is `<emit-form> = Σ₀(a) + Maj(a,b,c) = ` the `T2` local of the FIPS
180-4 round engine that the `sha2-*` chain step `F` runs.

## Front gap note (honest)

`Σ₀` is a *modular-rotate* `Σ` (`rotr` only), so it composes cleanly; the chain
step's `T1` half additionally folds in the round constant `K[t]` and schedule
word `W[t]` (two extra `wrapping_add`s of opaque inputs). Both halves use only
`rotate_right`/`BitXor`/`BitAnd`/`wrapping_add` — all in the existing front
recognizer set — so **no front change is required**. We emit the state-driven
`T2` half as the hash-composition leaf; `T1` is the same shape with
two extra leaf inputs (`kt`, `wt`) and is recorded as the natural extension
(`t1Src`/`t1_compiles`) below.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxSlhdsaChain

open _root_.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## §1  The `T2` chain-step combiner source — `w = 32`, parameters `["a","b","c"]`

`T2 = Σ₀(a) + Maj(a,b,c)`, the state-driven half of the SHA-256 round the WOTS+
chain step `F` runs. Fully let-normalized: each operator its own `letBind` over
atom arguments, the `Σ₀` rotates and the `Maj` ANDs interleaved exactly as the
hax ANF produces, then the final `wrapping_add` of the two halves. -/

/-- The WOTS+ chain-step `T2 = Σ₀(a) + Maj(a,b,c)` combiner source as a hax
    `ImpExpr`, fully let-normalized, parameters `["a","b","c"]`
    (`nIn = 3`; `I 0 = a`, `I 1 = b`, `I 2 = c`). Composes the SHA-256 `Σ₀(a)`
    round component (`a ror 2 ⊕ a ror 13 ⊕ a ror 22`) and the `Maj(a,b,c)`
    component (`(a∧b) ⊕ (a∧c) ⊕ (b∧c)`) through an integer `wrapping_add`. -/
def t2Src : ImpExpr :=
  -- Σ₀(a)
  .letBind "s0" (.app "rotate_right" [.var "a", .lit (.int 2)])
   (.letBind "s1" (.app "rotate_right" [.var "a", .lit (.int 13)])
    (.letBind "s2" (.app "rotate_right" [.var "a", .lit (.int 22)])
     (.letBind "s01" (.app "BitXor" [.var "s0", .var "s1"])
      (.letBind "bs0" (.app "BitXor" [.var "s01", .var "s2"])
       -- Maj(a,b,c)
       (.letBind "ab" (.app "BitAnd" [.var "a", .var "b"])
        (.letBind "ac" (.app "BitAnd" [.var "a", .var "c"])
         (.letBind "bc" (.app "BitAnd" [.var "b", .var "c"])
          (.letBind "m01" (.app "BitXor" [.var "ab", .var "ac"])
           (.letBind "mj" (.app "BitXor" [.var "m01", .var "bc"])
            -- T2 = Σ₀(a) + Maj(a,b,c)
            (.letBind "t2" (.app "wrapping_add" [.var "bs0", .var "mj"])
             (.var "t2")))))))))))

/-- The explicit closed **emit form** the `T2` source denotes to, at `w = 32`.
    `Σ₀(a)` then `Maj(a,b,c)`, added: the state-driven half of the SHA-256 round
    the WOTS+ chain step `F` runs. -/
def t2Form (a b c : BitVec 32) : BitVec 32 :=
  let bs0 := a.rotateRight 2 ^^^ a.rotateRight 13 ^^^ a.rotateRight 22
  let mj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
  bs0 + mj

/-- The `T2` source denotes (under `denoteScalar`, parameters `["a","b","c"]`) to
    the emit form `t2Form`, reading `a = inpGet I 0`, `b = inpGet I 1`,
    `c = inpGet I 2`. The closed let-normalized body reduces definitionally:
    `rotate_right` is `rotateRight`, `BitXor` is `^^^`, `BitAnd` is `&&&`,
    `wrapping_add` is `+`. -/
theorem t2Src_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 32) :
    ImpExpr.denoteScalar ["a", "b", "c"] I t2Src (fun _ => none)
      = some (t2Form (inpGet I 0) (inpGet I 1) (inpGet I 2)) := by
  rfl

/-- The compile-from-hax pipeline succeeds on the `T2` combiner (`w = 32`, three
    parameters). -/
theorem t2_compileFromHax_isSome :
    (compileFromHax (w := 32) (nIn := 3) ["a", "b", "c"] t2Src).isSome := by
  native_decide

/-- **SLH-DSA WOTS+ chain-step `T2` combiner emitted by the verified compiler.**
    There is a compiled `Com jasminDialect` `c` with
    `compileFromHax ["a","b","c"] t2Src = some c`, and for every triple
    `(a,b,c)`, `c`'s `BitVec 32` denotation (under the input valuation
    `![a,b,c]`) is exactly the emit form `t2Form` — the SHA-256 round
    quantity `Σ₀(a) + Maj(a,b,c)`. Routed through the C3 per-primitive
    obligation `compileFromHax_meets_spec`. This is the hash-composition
    Category-C fan-out: the emitted leaf **composes two SHA-256 round
    components** through an integer add. The tie onto the FIPS-180-4 round
    engine `Sha256Verified.sha256RoundVerified` (reusing the already-tied
    `Σ₀`/`Maj`) is `t2Form_eq_round_t2` (companion module). -/
theorem t2_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 32 3 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 3) ["a", "b", "c"] t2Src = some prog ∧
      ∀ (a b c : BitVec 32),
        prog.denote (inputValuation 32 3 ![a, b, c])
          = t2Form a b c := by
  set prog := (compileFromHax (w := 32) (nIn := 3) ["a", "b", "c"] t2Src).get
    t2_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 32) (nIn := 3) ["a", "b", "c"] t2Src = some prog :=
    (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro a b c
  have hspec : ImpExpr.denoteScalar ["a", "b", "c"] ![a, b, c] t2Src (fun _ => none)
      = some (t2Form a b c) := by
    have h := t2Src_denoteScalar (nIn := 3) ![a, b, c]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using! h
  exact compileFromHax_meets_spec (w := 32) (nIn := 3) ["a", "b", "c"]
    ![a, b, c] t2Src _ hc hspec

/-! ## §2  The `T1` chain-step combiner — the schedule/constant-folding half

`T1 = h + Σ₁(e) + Ch(e,f,g) + K[t] + W[t]`. Same straight-line ARX shape as `T2`
plus `Σ₁`/`Ch` (instead of `Σ₀`/`Maj`) and three extra `wrapping_add`s folding in
`h`, the round constant `kt`, and the schedule word `wt`. Parameters
`["e","f","g","h","kt","wt"]` (`nIn = 6`). Recorded for completeness — the full
SHA-256 round the WOTS+ chain step runs is `a' = T1 + T2`, `e' = d + T1`. -/

/-- The WOTS+ chain-step `T1 = h + Σ₁(e) + Ch(e,f,g) + kt + wt` combiner source as
    a hax `ImpExpr`, fully let-normalized, parameters `["e","f","g","h","kt","wt"]`
    (`nIn = 6`). The complement in `Ch` is desugared as `BitXor[e, lit 2³²−1]`. -/
def t1Src : ImpExpr :=
  -- Σ₁(e)
  .letBind "r0" (.app "rotate_right" [.var "e", .lit (.int 6)])
   (.letBind "r1" (.app "rotate_right" [.var "e", .lit (.int 11)])
    (.letBind "r2" (.app "rotate_right" [.var "e", .lit (.int 25)])
     (.letBind "r01" (.app "BitXor" [.var "r0", .var "r1"])
      (.letBind "bs1" (.app "BitXor" [.var "r01", .var "r2"])
       -- Ch(e,f,g) = (e∧f) ⊕ (¬e∧g), with ¬e = e ⊕ 0xFFFFFFFF
       (.letBind "ones" (.lit (.int 4294967295))
        (.letBind "ne" (.app "BitXor" [.var "e", .var "ones"])
         (.letBind "ef" (.app "BitAnd" [.var "e", .var "f"])
          (.letBind "neg" (.app "BitAnd" [.var "ne", .var "g"])
           (.letBind "chv" (.app "BitXor" [.var "ef", .var "neg"])
            -- T1 = h + Σ₁(e) + Ch(e,f,g) + kt + wt
            (.letBind "u0" (.app "wrapping_add" [.var "h", .var "bs1"])
             (.letBind "u1" (.app "wrapping_add" [.var "u0", .var "chv"])
              (.letBind "u2" (.app "wrapping_add" [.var "u1", .var "kt"])
               (.letBind "t1" (.app "wrapping_add" [.var "u2", .var "wt"])
                (.var "t1"))))))))))))))

/-- The explicit closed **emit form** the `T1` source denotes to, at `w = 32`. -/
def t1Form (e f g h kt wt : BitVec 32) : BitVec 32 :=
  let bs1 := e.rotateRight 6 ^^^ e.rotateRight 11 ^^^ e.rotateRight 25
  let chv := (e &&& f) ^^^ ((~~~e) &&& g)
  h + bs1 + chv + kt + wt

/-- The `T1` source denotes (under `denoteScalar`, parameters
    `["e","f","g","h","kt","wt"]`) to the emit form `t1Form`. The desugared
    `e ^^^ 0xFFFFFFFF` collapses to `~~~e` via `BitVec.xor_allOnes`. -/
theorem t1Src_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 32) :
    ImpExpr.denoteScalar ["e", "f", "g", "h", "kt", "wt"] I t1Src (fun _ => none)
      = some (t1Form (inpGet I 0) (inpGet I 1) (inpGet I 2)
                (inpGet I 3) (inpGet I 4) (inpGet I 5)) := by
  have e : ImpExpr.denoteScalar ["e", "f", "g", "h", "kt", "wt"] I t1Src (fun _ => none)
      = some (
        let bs1 := (inpGet I 0).rotateRight 6 ^^^ (inpGet I 0).rotateRight 11
                     ^^^ (inpGet I 0).rotateRight 25
        let chv := (inpGet I 0 &&& inpGet I 1)
                     ^^^ ((inpGet I 0 ^^^ BitVec.ofNat 32 4294967295) &&& inpGet I 2)
        inpGet I 3 + bs1 + chv + inpGet I 4 + inpGet I 5) := by
    rfl
  rw [e, t1Form, show (BitVec.ofNat 32 4294967295) = BitVec.allOnes 32 from by decide,
    BitVec.xor_allOnes]

/-- The compile-from-hax pipeline succeeds on the `T1` combiner (`w = 32`, six
    parameters). -/
theorem t1_compileFromHax_isSome :
    (compileFromHax (w := 32) (nIn := 6) ["e", "f", "g", "h", "kt", "wt"] t1Src).isSome := by
  native_decide

/-- **SLH-DSA WOTS+ chain-step `T1` combiner emitted by the verified compiler.**
    The schedule/constant-folding half of the SHA-256 round, composing the `Σ₁`
    and `Ch` round components plus the three `wrapping_add`s of `h`, `kt`, `wt`.
    Routed through `compileFromHax_meets_spec`. -/
theorem t1_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 32 6 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 6) ["e", "f", "g", "h", "kt", "wt"] t1Src = some prog ∧
      ∀ (e f g h kt wt : BitVec 32),
        prog.denote (inputValuation 32 6 ![e, f, g, h, kt, wt])
          = t1Form e f g h kt wt := by
  set prog := (compileFromHax (w := 32) (nIn := 6) ["e", "f", "g", "h", "kt", "wt"] t1Src).get
    t1_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 32) (nIn := 6) ["e", "f", "g", "h", "kt", "wt"] t1Src
      = some prog := (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro e f g h kt wt
  have hspec : ImpExpr.denoteScalar ["e", "f", "g", "h", "kt", "wt"]
      ![e, f, g, h, kt, wt] t1Src (fun _ => none) = some (t1Form e f g h kt wt) := by
    have hh := t1Src_denoteScalar (nIn := 6) ![e, f, g, h, kt, wt]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four] using! hh
  exact compileFromHax_meets_spec (w := 32) (nIn := 6) ["e", "f", "g", "h", "kt", "wt"]
    ![e, f, g, h, kt, wt] t1Src _ hc hspec

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxSlhdsaChain
