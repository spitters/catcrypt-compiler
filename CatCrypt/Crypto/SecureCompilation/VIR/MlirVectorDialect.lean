/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.Core

/-!
# A *denoting* MLIR `vector` dialect in the VIR framework ("AVX-in-MLIR")

> **STATUS — MLIR-CORRESPONDENCE LAYER, NOT THE EMIT PATH.** `rfl`
> semantic-agreement lemmas proving CatCrypt ops match upstream MLIR `vector`; NO
> lowering out, ZERO emit traffic. Duplicates `vec128Dialect` / `ymm256Dialect`,
> which ARE the real SIMD substrate (and carry the descent to x86). See
> `CatCrypt/Crypto/SecureCompilation/VIR/DIALECTS.md`.

This is the SIMD analogue of `MlirArithDialect.lean` / `MlirMemrefDialect.lean`
/ `MlirPolynomialDialect.lean`. Those files supply denoting MLIR `arith` /
`memref` / `polynomial` dialects for the scalar / array / polynomial fragments
of the CatCrypt front. Here we supply a denoting MLIR **`vector`** dialect over
fixed-width integer lanes — the foundation for emitting a primitive (the ML-KEM
NTT butterflies, coefficient-wise poly add, …) as MLIR `vector`-dialect ops that
`mlir-opt`'s `vector → x86vector`/`llvm` lowering turns into AVX2 SIMD.

The point of *denoting* the dialect (rather than treating the vectorized op as a
trusted leaf) is the **vectorization-is-semantics-preserving** theorem: a vector
op denotes to the *elementwise* scalar op. That is exactly the fact a sound
"scalar elementwise loop ⇄ vector op" rewrite needs, in both directions:

Official MLIR dialect attribution: element-wise integer arithmetic on a vector
type IS the `arith` dialect (`arith.addi : vector<16xi16>` — arith ops are
shaped-type-polymorphic; there is no `vector.addi`). Only `splat` is a
`vector`-dialect op here. AVX target: `x86vector` + `-convert-vector-to-llvm`.

| upstream MLIR op | denotation (`a b : Fin lanes → BitVec w`) | per-lane meaning |
|------------------|-------------------------------------------|------------------|
| `arith.addi : vector<lanes×iw>` | `fun i => a i + b i`           | scalar `BitVec.+` |
| `arith.subi : vector<lanes×iw>` | `fun i => a i - b i`           | scalar `BitVec.-` |
| `arith.muli : vector<lanes×iw>` | `fun i => a i * b i`           | scalar `BitVec.*` |
| `arith.andi : vector<lanes×iw>` | `fun i => a i &&& b i`         | scalar `BitVec.&&&` |
| `arith.xori : vector<lanes×iw>` | `fun i => a i ^^^ b i`         | scalar `BitVec.^^^` |
| `vector.splat`   | `fun _ => x`                               | broadcast a scalar |

## Types (`VecTy`)

We use a **small local** type alphabet rather than reusing `CryptoTy`, so the
vector type is first-class:

* `sword w`     — a scalar fixed-width integer, `⟦·⟧ = BitVec w`
* `vec lanes w` — `lanes` parallel `BitVec w` lanes, `⟦·⟧ = Fin lanes → BitVec w`

A `vec lanes w` is the dialect-level model of an MLIR `vector<lanes x iw>`
SSA value; on x86 a `vec 16 16` (`vector<16xi16>`) is one AVX2 `__m256i`.

## What is proven here

1. The dialect `mlirVectorDialect` (`§1`–`§2`): `VecTy`, `VecOp`, the
   `DialectSignature`, and an **elementwise** `DialectDenote`.
2. The per-op **elementwise-agreement** lemmas (`§3`):
   `agree_vaddi`/`vsubi`/`vmuli`/`vandi`/`vxori`/`vsplat` — each says the vector
   op at lane `i` equals the scalar `BitVec` op on the two lanes. These justify
   lowering a scalar elementwise loop to a single vector op (and back).
3. The **verified vectorized poly add** proof of concept (`§4`):
   `polyAdd_vectorized_eq` shows the ML-KEM coefficient-wise add of two
   256-coefficient polynomials (`Fin 256 → BitVec 16`), *computed as 16 lanes ×
   `vec 16 16` vector adds*, equals the scalar 256-wide coefficient add. The
   NTT butterfly has the same elementwise shape (a lane-parallel
   add/sub/Montgomery-mul); the poly-add PoC is the representative instance.

The closing note (`§5`) states the path to the full result: emit the NTT
butterflies as `mlirVectorDialect` ops (not `extCall` leaves), run
`mlir-opt -convert-vector-to-llvm` / the x86vector AVX lowering → AVX2, and
carry the CompPoly `realNttMul_negacyclic_coeff` proof through the vectorized
form. This file is the dialect + the elementwise agreement + the poly-add PoC;
the full vectorized-NTT emit + the `mlir-opt` AVX pass are the follow-ons.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.MlirVectorDialect

open CatCrypt.Crypto.SecureCompilation.VIR

/-! ## 1. Types

A small local `Ty` alphabet: scalar integers and lane vectors. Making `vec` a
first-class `Ty` (denoting to `Fin lanes → BitVec w`) is what lets a `vector.*`
op be type-checked and denoted as a single SSA value. -/

/-- The vector dialect's value-type alphabet.

* `sword w`     — a scalar fixed-width integer (`iw`), `⟦·⟧ = BitVec w`.
* `vec lanes w` — an MLIR `vector<lanes x iw>`, i.e. `lanes` parallel `BitVec w`
  lanes, `⟦·⟧ = Fin lanes → BitVec w`. (On x86, `vec 16 16` is one AVX2 register.) -/
inductive VecTy where
  /-- A scalar `iw`. -/
  | sword (w : Nat)
  /-- A lane vector `vector<lanes x iw>`. -/
  | vec (lanes : Nat) (w : Nat)
  deriving DecidableEq

/-- Total denotation of `VecTy`. A scalar is a `BitVec w`; a lane vector is
    `lanes` parallel `BitVec w`, modelled as `Fin lanes → BitVec w`. -/
@[reducible] instance : TyDenote VecTy where
  denote
    | .sword w => BitVec w
    | .vec lanes w => Fin lanes → BitVec w

/-! ## 2. The dialect, signature and denotation

The vector ops we model. Lane count `lanes` and element width `w` are carried
as op parameters, mirroring an MLIR `vector<lanes x iw>` static type. The
binary ops are lane-parallel; `vsplat`/`vbroadcast` build a vector from a
scalar / from lane 0. We also include the scalar `addi` op so the file is
self-contained as a reference for the per-lane scalar operation. -/

/-- Operation tags, each mapped to its registered UPSTREAM MLIR opcode. NB the
    official MLIR split: **element-wise integer arithmetic on a vector type is
    the `arith` dialect** (its ops are shaped-type-polymorphic — `arith.addi :
    vector<16xi16>`), there is *no* `vector.addi`. The `vector` dialect proper
    holds the SIMD data-movement ops (`vector.splat`/`broadcast`, `shuffle`,
    `transpose`, `fma`, `reduction`, `transfer_read/write`). So below: the
    lane-parallel binary ops ARE `arith.*` at vector type; only `vsplat` is a
    `vector.*` op. (Full NTT vectorisation additionally needs
    `vector.shuffle`/`transpose`/`fma`; AVX target via `x86vector` +
    `-convert-vector-to-llvm`.) -/
inductive VecOp where
  -- element-wise integer arithmetic = `arith.<op> : vector<lanes x iw>` (arith dialect)
  /-- `arith.addi : vector<lanes x iw>` (element-wise add). -/
  | vaddi (lanes w : Nat)
  /-- `arith.subi : vector<lanes x iw>`. -/
  | vsubi (lanes w : Nat)
  /-- `arith.muli : vector<lanes x iw>`. -/
  | vmuli (lanes w : Nat)
  /-- `arith.andi : vector<lanes x iw>`. -/
  | vandi (lanes w : Nat)
  /-- `arith.ori : vector<lanes x iw>` (element-wise or). -/
  | vori (lanes w : Nat)
  /-- `arith.xori : vector<lanes x iw>`. -/
  | vxori (lanes w : Nat)
  /-- `arith.shli : vector<lanes x iw>` by a static shift amount `n`
      broadcast across all lanes. -/
  | vshli (lanes w : Nat) (n : Nat)
  /-- `arith.shrui : vector<lanes x iw>` (logical right-shift) by a static
      shift amount `n` broadcast across all lanes. -/
  | vshri (lanes w : Nat) (n : Nat)
  -- `vector` dialect ops
  /-- `vector.splat`: broadcast a scalar `iw` to all `lanes`. -/
  | vsplat (lanes w : Nat)
  /-- `vector.extract`: project lane `idx` of a `vec lanes w` to a scalar
      `BitVec w`. Static lane index, matching MLIR's `vector.extract %v[idx]`. -/
  | vextract (lanes w : Nat) (idx : Nat)
  -- the scalar reference op (a single lane), for per-lane agreement
  /-- `arith.addi` (scalar): the per-lane operation that `vaddi` parallelises. -/
  | addi (w : Nat)
  deriving DecidableEq

/-- The local MLIR `vector` dialect: `Op` is `VecOp`, `Ty` is `VecTy`. -/
@[reducible] def mlirVectorDialect : Dialect :=
  { Op := VecOp, Ty := VecTy }

/-- Operation signatures: argument types + return type. The lane-parallel ops
    take/return `vec lanes w`; `vsplat` takes a scalar and returns a vector;
    `vbroadcast` takes/returns a vector; scalar `addi` is the `sword`-typed
    reference. -/
@[reducible] instance instMlirVectorSignature :
    DialectSignature mlirVectorDialect where
  sig op := match op with
    | .vaddi lanes w | .vsubi lanes w | .vmuli lanes w
    | .vandi lanes w | .vori lanes w | .vxori lanes w =>
        [.vec lanes w, .vec lanes w]
    | .vshli lanes w _ | .vshri lanes w _ => [.vec lanes w]
    | .vsplat _ w => [.sword w]
    | .vextract lanes w _ => [.vec lanes w]
    | .addi w => [.sword w, .sword w]
  ret op := match op with
    | .vaddi lanes w | .vsubi lanes w | .vmuli lanes w
    | .vandi lanes w | .vori lanes w | .vxori lanes w => .vec lanes w
    | .vshli lanes w _ | .vshri lanes w _ => .vec lanes w
    | .vsplat lanes w => .vec lanes w
    | .vextract _ w _ => .sword w
    | .addi w => .sword w

/-- Operation denotation: the **standard MLIR `vector` integer semantics**,
    which is *elementwise* on lanes. Each lane-parallel op applies the matching
    scalar `BitVec` operation lane-by-lane; `vsplat`/`vbroadcast` build a
    constant vector; scalar `addi` is the single-lane `BitVec.+`. -/
instance mlirVectorDenote : DialectDenote mlirVectorDialect where
  denote op := match op with
    | .vaddi lanes w => fun args =>
        let a : Fin lanes → BitVec w := args.head
        let b : Fin lanes → BitVec w := args.tail.head
        fun i => a i + b i
    | .vsubi lanes w => fun args =>
        let a : Fin lanes → BitVec w := args.head
        let b : Fin lanes → BitVec w := args.tail.head
        fun i => a i - b i
    | .vmuli lanes w => fun args =>
        let a : Fin lanes → BitVec w := args.head
        let b : Fin lanes → BitVec w := args.tail.head
        fun i => a i * b i
    | .vandi lanes w => fun args =>
        let a : Fin lanes → BitVec w := args.head
        let b : Fin lanes → BitVec w := args.tail.head
        fun i => a i &&& b i
    | .vori lanes w => fun args =>
        let a : Fin lanes → BitVec w := args.head
        let b : Fin lanes → BitVec w := args.tail.head
        fun i => a i ||| b i
    | .vxori lanes w => fun args =>
        let a : Fin lanes → BitVec w := args.head
        let b : Fin lanes → BitVec w := args.tail.head
        fun i => a i ^^^ b i
    | .vshli lanes w n => fun args =>
        let a : Fin lanes → BitVec w := args.head
        (fun i => a i <<< n : Fin lanes → BitVec w)
    | .vshri lanes w n => fun args =>
        let a : Fin lanes → BitVec w := args.head
        (fun i => BitVec.ushiftRight (a i) n : Fin lanes → BitVec w)
    | .vsplat lanes w => fun args =>
        let x : BitVec w := args.head
        (fun _ => x : Fin lanes → BitVec w)
    | .vextract lanes w idx => fun args =>
        -- Project lane `idx` of the input vector. If `idx ≥ lanes` (or
        -- `lanes = 0`) the op is out of range in MLIR; we make the
        -- denotation total by returning `0` in that case, otherwise
        -- `a ⟨idx, _⟩`. This matches the "out-of-range extract is
        -- poison" upstream semantics in the sense that consumers should
        -- only construct in-range `vextract` ops; the total fallback is
        -- denotation-level only.
        let a : Fin lanes → BitVec w := args.head
        if h : idx < lanes then a ⟨idx, h⟩ else (0 : BitVec w)
    | .addi w => fun args =>
        let a : BitVec w := args.head
        let b : BitVec w := args.tail.head
        a + b

/-! ## 3. Per-op elementwise agreement

**Vectorization is semantics-preserving.** For each lane-parallel vector op,
its denotation *at lane `i`* equals the matching scalar `BitVec` op applied to
the two lanes. This is the per-op crux that justifies lowering a scalar
elementwise loop to a single SIMD vector op (and the reverse — scalarising a
vector op back to a per-lane loop). Every lemma closes by `rfl`: the
denotations are definitionally the elementwise functions. -/

section Agreement

variable (lanes w : Nat)

/-- `vector.addi` is the elementwise scalar add: at lane `i`,
    `(vaddi).denote a b i = a i + b i`. -/
theorem agree_vaddi (a b : Fin lanes → BitVec w) (i : Fin lanes) :
    DialectDenote.denote (d := mlirVectorDialect) (.vaddi lanes w)
        (.cons a (.cons b .nil)) i
      = a i + b i := rfl

/-- `vector.subi` is the elementwise scalar sub. -/
theorem agree_vsubi (a b : Fin lanes → BitVec w) (i : Fin lanes) :
    DialectDenote.denote (d := mlirVectorDialect) (.vsubi lanes w)
        (.cons a (.cons b .nil)) i
      = a i - b i := rfl

/-- `vector.muli` is the elementwise scalar mul. -/
theorem agree_vmuli (a b : Fin lanes → BitVec w) (i : Fin lanes) :
    DialectDenote.denote (d := mlirVectorDialect) (.vmuli lanes w)
        (.cons a (.cons b .nil)) i
      = a i * b i := rfl

/-- `vector.andi` is the elementwise scalar and. -/
theorem agree_vandi (a b : Fin lanes → BitVec w) (i : Fin lanes) :
    DialectDenote.denote (d := mlirVectorDialect) (.vandi lanes w)
        (.cons a (.cons b .nil)) i
      = a i &&& b i := rfl

/-- `vector.ori` is the elementwise scalar or. -/
theorem agree_vori (a b : Fin lanes → BitVec w) (i : Fin lanes) :
    DialectDenote.denote (d := mlirVectorDialect) (.vori lanes w)
        (.cons a (.cons b .nil)) i
      = a i ||| b i := rfl

/-- `vector.xori` is the elementwise scalar xor. -/
theorem agree_vxori (a b : Fin lanes → BitVec w) (i : Fin lanes) :
    DialectDenote.denote (d := mlirVectorDialect) (.vxori lanes w)
        (.cons a (.cons b .nil)) i
      = a i ^^^ b i := rfl

/-- `arith.shli @ vector<...>` is the elementwise scalar left shift by `n`. -/
theorem agree_vshli (a : Fin lanes → BitVec w) (n : Nat) (i : Fin lanes) :
    DialectDenote.denote (d := mlirVectorDialect) (.vshli lanes w n)
        (.cons a .nil) i
      = a i <<< n := rfl

/-- `arith.shrui @ vector<...>` is the elementwise scalar logical right
    shift by `n`. -/
theorem agree_vshri (a : Fin lanes → BitVec w) (n : Nat) (i : Fin lanes) :
    DialectDenote.denote (d := mlirVectorDialect) (.vshri lanes w n)
        (.cons a .nil) i
      = BitVec.ushiftRight (a i) n := rfl

/-- `vector.splat` broadcasts a scalar to every lane. -/
theorem agree_vsplat (x : BitVec w) (i : Fin lanes) :
    DialectDenote.denote (d := mlirVectorDialect) (.vsplat lanes w)
        (.cons x .nil) i
      = x := rfl

/-- `vector.extract` at an in-range lane index `idx < lanes` returns
    `a ⟨idx, _⟩`. -/
theorem agree_vextract_lt
    (a : Fin lanes → BitVec w) (idx : Nat) (h : idx < lanes) :
    DialectDenote.denote (d := mlirVectorDialect) (.vextract lanes w idx)
        (.cons a .nil)
      = a ⟨idx, h⟩ := by
  show (if h' : idx < lanes then a ⟨idx, h'⟩ else (0 : BitVec w)) = _
  simp [h]

/-- The lane-parallel `vaddi` denotes to the elementwise lift of the *scalar*
    `addi` op: at every lane `i`, the vector op equals the scalar dialect op on
    the two lanes. This is the explicit "vector = elementwise scalar" statement
    relating the two ops of the dialect. -/
theorem agree_vaddi_scalar (a b : Fin lanes → BitVec w) (i : Fin lanes) :
    DialectDenote.denote (d := mlirVectorDialect) (.vaddi lanes w)
        (.cons a (.cons b .nil)) i
      = DialectDenote.denote (d := mlirVectorDialect) (.addi w)
        (.cons (a i) (.cons (b i) .nil)) := rfl

end Agreement

/-! ## 3.1 Com-level smoke witness

Analogue of `MLIRBackend/ComToVeir.lean`'s `smokeAddProgram` over scalar
`mlirArithDialect`, but at the vector dialect. We build a 3-instruction
program `let a = const-vec₁; let b = const-vec₂; let r = vaddi a b; ret r`
using a `vsplat` to produce each constant vector from a scalar literal
(this avoids needing a separate constant-vector op). The denotation
reduces by `rfl` once we step through the `Com.var` clauses. -/

/-- A 3-instruction VIR program over `mlirVectorDialect`, parametrised by
    two scalar inputs (in the initial context): splat both, then `vaddi`.
    Denotation: the lane-wise sum of the two splatted constants. -/
def smokeAddProgram (lanes w : Nat) :
    Com mlirVectorDialect [VecTy.sword w, VecTy.sword w] (VecTy.vec lanes w) :=
  -- Γ₀ = [sword w, sword w]; here = c1 (de-bruijn 0), there here = c2 (1).
  -- let va = vsplat c1
  Com.var
    (Expr.mk (d := mlirVectorDialect)
      (Γ := [VecTy.sword w, VecTy.sword w]) (t := VecTy.vec lanes w)
      (VecOp.vsplat lanes w) rfl
      (HVector.cons Ctxt.Var.here HVector.nil)) <|
  -- let vb = vsplat c2 (now Γ = [vec, sword, sword])
  Com.var
    (Expr.mk (d := mlirVectorDialect)
      (Γ := [VecTy.vec lanes w, VecTy.sword w, VecTy.sword w])
      (t := VecTy.vec lanes w)
      (VecOp.vsplat lanes w) rfl
      (HVector.cons (Ctxt.Var.there (Ctxt.Var.there Ctxt.Var.here))
        HVector.nil)) <|
  -- let r = vaddi vb va (vb at 0, va at 1)
  Com.var
    (Expr.mk (d := mlirVectorDialect)
      (Γ := [VecTy.vec lanes w, VecTy.vec lanes w,
             VecTy.sword w, VecTy.sword w])
      (t := VecTy.vec lanes w)
      (VecOp.vaddi lanes w) rfl
      (HVector.cons (Ctxt.Var.there Ctxt.Var.here)
        (HVector.cons Ctxt.Var.here HVector.nil))) <|
  Com.ret Ctxt.Var.here

/-- Smoke test: evaluating the 3-instruction vector program at scalars
    `c1`, `c2` produces a vector whose every lane is `c1 + c2`. -/
theorem smokeAddProgram_denote (lanes w : Nat) (c1 c2 : BitVec w) :
    (smokeAddProgram lanes w).denote
        (HVector.cons c1 (HVector.cons c2 HVector.nil))
      = (fun _ : Fin lanes => c1 + c2) := by
  unfold smokeAddProgram
  simp only [Com.denote, Expr.denote, Ctxt.Valuation.extend]
  rfl

/-- Concrete witness for the smoke program at lanes=8, w=16:
    splat 3 + splat 5 = (lane ↦ 8). -/
example :
    (smokeAddProgram 8 16).denote
        (HVector.cons (3 : BitVec 16) (HVector.cons (5 : BitVec 16) HVector.nil))
      = (fun _ : Fin 8 => (8 : BitVec 16)) := by
  rw [smokeAddProgram_denote]
  rfl

/-! ## 4. The verified vectorized poly add (proof of concept)

This section applies the dialect to an ML-KEM-shaped operation: coefficient-wise
addition of two 256-coefficient polynomials (`Fin 256 → BitVec 16`, the ML-KEM
`R_q` representation). The scalar version is the obvious pointwise add. The
*vectorized* version splits the 256 coefficients into `16` chunks of `16`
lanes, runs a `vec 16 16` `vaddi` on each chunk (one AVX2 `__m256i` add), and
reassembles. We prove the two compute the same `Fin 256 → BitVec 16`.

The lane ↔ coefficient bijection is `coeff = chunk * 16 + lane`, i.e. the
standard `divMod 16` decomposition of `Fin 256 ≃ Fin 16 × Fin 16`. -/

/-- Number of coefficients in an ML-KEM polynomial. -/
abbrev nCoeffs : Nat := 256

/-- AVX2 lane width for `i16`: a `__m256i` holds `16` `BitVec 16` lanes. -/
abbrev nLanes : Nat := 16

/-- Number of `vec 16 16` chunks needed to cover the 256 coefficients. -/
abbrev nChunks : Nat := 16

/-- Scalar (reference) coefficient-wise add of two 256-coefficient polynomials:
    the pointwise `BitVec 16` sum. This is the meaning the vectorized form must
    preserve. -/
def polyAddScalar (a b : Fin nCoeffs → BitVec 16) : Fin nCoeffs → BitVec 16 :=
  fun i => a i + b i

/-- Slice a 256-coefficient poly into chunk `c`: the `vec 16 16` whose lane `l`
    is coefficient `c * 16 + l`. (`Fin.mk` is total because `c * 16 + l < 256`
    for `c, l < 16`.) -/
def chunk (a : Fin nCoeffs → BitVec 16) (c : Fin nChunks) : Fin nLanes → BitVec 16 :=
  fun l => a ⟨c.val * nLanes + l.val, by
    have hc : c.val < nChunks := c.isLt
    have hl : l.val < nLanes := l.isLt
    -- c*16 + l < 16*16 = 256
    simp only [nCoeffs, nChunks, nLanes] at *; omega⟩

/-- The **vectorized** coefficient-wise add: for each of the 16 chunks, run a
    `vec 16 16` `vector.addi`, then reassemble the 256 coefficients. The result
    is read back at coefficient `i` by splitting `i = (i / 16) * 16 + (i % 16)`
    into chunk index and lane index. -/
def polyAddVectorized (a b : Fin nCoeffs → BitVec 16) : Fin nCoeffs → BitVec 16 :=
  fun i =>
    -- chunk index and lane index of coefficient `i`
    let c : Fin nChunks := ⟨i.val / nLanes, by
      have : i.val < nCoeffs := i.isLt
      simp only [nCoeffs, nChunks, nLanes] at *; omega⟩
    let l : Fin nLanes := ⟨i.val % nLanes, Nat.mod_lt _ (by decide)⟩
    -- the single SIMD add of the two 16-lane chunks, read at lane `l`
    DialectDenote.denote (d := mlirVectorDialect) (.vaddi nLanes 16)
      (.cons (chunk a c) (.cons (chunk b c) .nil)) l

/-- **Verified vectorized poly add.** The 256-wide coefficient-wise add computed
    as `16 × vec 16 16` SIMD adds equals the scalar coefficient-wise add.

    Proof: `funext i`; the vector op at lane `l = i % 16` of chunk `c = i / 16`
    is `chunk a c l + chunk b c l` (per-lane agreement, `agree_vaddi`), and
    `chunk a c l = a ⟨c*16 + l, _⟩ = a ⟨(i/16)*16 + (i%16), _⟩ = a i` by the
    divmod identity. Index equality is `Fin.ext` + `omega`; the rest is `rfl`. -/
theorem polyAdd_vectorized_eq (a b : Fin nCoeffs → BitVec 16) :
    polyAddVectorized a b = polyAddScalar a b := by
  funext i
  -- Both sides at coefficient `i`. The vector op reduces (definitionally, by
  -- `agree_vaddi`) to the sum of the two chunk lanes; rewrite those back to the
  -- original coefficients via the divmod identity on the indices.
  show (chunk a _ _ + chunk b _ _) = a i + b i
  have hidx : (⟨i.val / nLanes * nLanes + i.val % nLanes, by
      have : i.val < nCoeffs := i.isLt
      simp only [nCoeffs, nLanes] at *; omega⟩ : Fin nCoeffs) = i := by
    apply Fin.ext
    show i.val / nLanes * nLanes + i.val % nLanes = i.val
    simp only [nLanes]; omega
  simp only [chunk]
  rw [hidx]

/-! ## 5. Closing note: the path to the full vectorized NTT

This file delivers the **foundation**: a denoting MLIR `vector` dialect, the
per-op **elementwise-agreement** lemmas (`§3`) certifying that each SIMD vector
op denotes to the matching scalar `BitVec` op applied lane-by-lane, and the
**verified vectorized poly add** proof of concept (`polyAdd_vectorized_eq`,
`§4`) — the 256-wide coefficient add as `16 × vec 16 16` AVX2 adds equals the
scalar add, with no open goals and no extra axioms.

The **full result** (the follow-ons) is:

1. **Emit the NTT butterflies as `mlirVectorDialect` ops.** The Cooley–Tukey /
   Gentleman–Sande butterfly is `(a, b) ↦ (a + t, a - t)` with
   `t = montgomery_mul(b, ζ)`. Each layer applies that to lane-aligned chunks of
   the 256 coefficients — exactly the elementwise shape of `polyAdd_vectorized_eq`
   (here `vaddi`/`vsubi` plus a lane-parallel Montgomery `vmuli`+reduce). So the
   butterfly emits as `vec 16 16` `vaddi`/`vsubi`/`vmuli` ops instead of `extCall`
   leaves, bringing the vectorized primitive *into* the verified emit.

2. **Run the `mlir-opt` AVX lowering.** `mlir-opt -convert-vector-to-llvm`
   (or the `x86vector` AVX-specific lowering) turns each `vector<16 x i16>` op
   into an AVX2 `__m256i` instruction. This is the SIMD codegen step; the
   dialect here is precisely what that pass consumes.

3. **Carry the CompPoly proof through the vectorized form.** The negacyclic
   correctness theorem `realNttMul_negacyclic_coeff` (the deep schoolbook = NTT
   fact, already a CompPoly obligation) composes with the per-lane agreement of
   `§3`: each butterfly layer's vector op equals its scalar elementwise layer
   (the `agree_*` family generalised to `vsubi`/`vmuli` and the divmod chunking
   of `§4`), so the *vectorized* NTT denotes to the *scalar* NTT, and the
   existing negacyclic proof transfers verbatim.

Scope: this module is the **dialect + the elementwise agreement + the
poly-add PoC**. The full vectorized-NTT *emit* and the `mlir-opt` AVX *pass* are
outside it; the semantic obligation they rest on (the
"vector op = elementwise scalar op" agreement) is discharged here. -/

end CatCrypt.Crypto.SecureCompilation.VIR.MlirVectorDialect
