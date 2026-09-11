/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.X86Intrinsics
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.X86Intrinsics
public meta import CatCrypt.Crypto.Util.Gf16
public import CatCrypt.Crypto.Util.Gf16
public meta import CatCrypt.Crypto.MAYO.MqEvalVerified
public import CatCrypt.Crypto.MAYO.MqEvalVerified

/-!
# MAYO `.jinc` scalar-leaf body — Lean model + verified-GF equivalence

This file models the **scalar** body of MAYO's rustcmd-link `.jinc` shim
(`bench/mayo_compare/include/mayo_leaves.jinc`, `mayo_quadform_n8`) as a
concrete Lean function and proves it equals `MqEvalVerified.mqEvalN8`.

## What the `.jinc` body does

The scalar body has two pieces (cf. `mayo_leaves.jinc:29-100`):

1. `gf16_mul_scalar(a, b)` — bit-serial Russian-peasant GF(16) multiply.
   4 rounds of: extract bit `i` of `b`, AND it as a mask onto `a`, XOR
   into the running accumulator, then shift `a` left by 1 with reduction
   by `0x13 = x^4+x+1` on overflow.
2. `mayo_quadform_n8(s, mat)` — double 8×8 loop computing
   `Σ_{j,l} A[j][l] · s[j] · s[l]`, with each multiply going through
   `gf16_mul_scalar` and the outer accumulator XOR-folded.

The Lean model in this file follows the exact same shape, but at the
`BitVec 8` / `BitVec 4` level — i.e. we hold values as `BitVec 4` (a
nibble in the low 4 bits of a byte) and compose the operations bit-by-
bit. The model is proved equal to `MqEvalVerified.mqEvalN8` over the
identity decoding `BitVec 4 ↔ Gf16`.

## Discharge route for the cross-side axiom

The MAYO bridge had one cross-side axiom

```
mayo_quadform_n8_eq_mqEvalN8 :
    mayoScalarToGf16 (mayo_quadform_n8 s mat) = mqEvalN8 (toVec s) (toVec mat)
```

We cannot remove this entirely (the LHS contains the opaque axiomatic
type `MayoVecN8 → MayoMat8x8 → MayoScalar`, so the equation lives in
Lean's axiom layer no matter what). What we CAN do is route the GF(16)
arithmetic content through a verified intermediate — namely,

```
   mayoQuadformJincModel : Vector Gf16 8 → Vector Gf16 64 → Gf16
```

— such that

```
   theorem mayoQuadformJincModel_eq_mqEvalN8 :
       mayoQuadformJincModel = MqEvalVerified.mqEvalN8     -- PROVED
```

reduces all the GF(16) algebra to `Gf16.mul`'s decision procedure. The
residual axiom is then a pure ABI claim — "the `.jinc` body's byte
encoding matches the verified-GF arithmetic" — with no GF(16) reasoning
left inside it.

## References

* `bench/mayo_compare/include/mayo_leaves.jinc` — the body we model
* `CatCrypt/Crypto/Util/Gf16.lean` — the verified GF(16) field
* `CatCrypt/Crypto/MAYO/MqEvalVerified.lean` — `mqEvalN8` over GF(16)
* `CatCrypt/Crypto/SecureCompilation/MLIR/VectorDialect/X86Intrinsics.lean`
  — the SIMD intrinsic catalog (used by the SIMD-variant model in §6)
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.MayoLeafProof

open CatCrypt.Util
open CatCrypt.Util.Gf16
open CatCrypt.Crypto.MAYO.MqEvalVerified

/-! ## §1. Bit-serial Russian-peasant GF(16) multiply — Lean transcription

The `.jinc` body's `gf16_mul_scalar(a, b)` follows the pseudocode

```
r  := 0
sh := a
bb := b
for i = 0 .. 3:
  bit_v := -(bb & 1)           // 0 or 0xFF
  prod  := sh & bit_v          // sh if bit_v=0xFF else 0
  r     := r ^ prod
  bb    := bb >> 1
  hi    := -((sh >> 3) & 1)    // 0 or 0xFF
  sh    := (sh << 1) ^ (hi & 0x3)
  sh    := sh & 0xf
return r & 0xf
```

The `0x3` mask encodes the reduction polynomial `x^4 + x + 1` (as a
4-bit residual when the leading `x^4` bit overflows: bit-4 of the
shifted value, if set, XORs `x + 1 = 0b0011 = 0x3` back into the low
nibble). Below we transcribe this at the `BitVec 4` width directly,
sidestepping the `BitVec 8`-padding the .jinc uses for register-fit. -/

/-- One round of the bit-serial GF(16) multiply at bit position `i`. -/
def gf16MulStep (i : Nat) (sh bb r : BitVec 4) : BitVec 4 × BitVec 4 × BitVec 4 :=
  let bit  : BitVec 4 := bb &&& 1#4
  -- bit_v := if bit=1 then 0xF else 0x0  (4-bit mask form of -bit)
  let mask : BitVec 4 := if bit == 1#4 then 0xF#4 else 0#4
  let prod : BitVec 4 := sh &&& mask
  let r'   : BitVec 4 := r ^^^ prod
  let bb'  : BitVec 4 := bb >>> 1
  -- Reduction step: take bit-3 of sh; if set, after the <<<1, XOR 0x3 back.
  let hi_bit : BitVec 4 := (sh >>> 3) &&& 1#4
  let hi_mask : BitVec 4 := if hi_bit == 1#4 then 0x3#4 else 0#4
  let sh_shift : BitVec 4 := sh <<< 1
  let sh' : BitVec 4 := sh_shift ^^^ hi_mask
  let _ := i  -- the loop index is unused after unrolling
  (sh', bb', r')

/-- The full 4-round bit-serial GF(16) multiply, as a Lean transcription of
    `gf16_mul_scalar` from `mayo_leaves.jinc`. -/
def gf16MulJinc (a b : BitVec 4) : BitVec 4 :=
  let (sh0, bb0, r0) := gf16MulStep 0 a b 0#4
  let (sh1, bb1, r1) := gf16MulStep 1 sh0 bb0 r0
  let (sh2, bb2, r2) := gf16MulStep 2 sh1 bb1 r1
  let (_sh3, _bb3, r3) := gf16MulStep 3 sh2 bb2 r2
  r3 &&& 0xF#4

/-- **Bit-serial vs Mathlib-shift-and-XOR equivalence.** The bit-serial
    `.jinc` multiply (transcribed at the BitVec 4 width) agrees with the
    verified `Gf16.mul` reference on the entire 16×16 input space.

    Proven by `decide` (256 cases, sub-second). -/
theorem gf16MulJinc_eq_Gf16_mul : ∀ a b : BitVec 4, gf16MulJinc a b = Gf16.mul a b := by
  decide

/-! ## §2. Lean model of the outer quadratic-form loop

The `.jinc` body's `mayo_quadform_n8` is

```
acc := 0
for j = 0 .. 7:
  sj := nibble(s, j)
  for l = 0 .. 7:
    aval := nibble(mat[j], l)
    sl   := nibble(s, l)
    prod := gf16_mul_scalar(gf16_mul_scalar(aval, sj), sl)
    acc  := acc ^ prod
return acc & 0xf
```

Translated to operate on `Vector Gf16 8` (the `s`) and `Vector Gf16 64`
(the `mat`, row-major) — the same shape as `MqEvalVerified.mqEvalN8`. -/

/-- The inner-loop body of the `.jinc` quadratic form at position `(j, l)`.
    Returns `A[j][l] · s[j] · s[l]` using the bit-serial Jinc multiply. -/
def jincInnerTerm (s : Vector Gf16 8) (mat : Vector Gf16 64) (j l : Fin 8) : Gf16 :=
  let sj   := s.get j
  let aval := mat.get ⟨j.val * 8 + l.val, by have := j.isLt; have := l.isLt; omega⟩
  let sl   := s.get l
  -- The .jinc body composes as gf16_mul(gf16_mul(aval, sj), sl).
  gf16MulJinc (gf16MulJinc aval sj) sl

/-- A row of the outer loop at index `j`: `Σ_l A[j][l] · s[j] · s[l]`. -/
def jincRowSum (s : Vector Gf16 8) (mat : Vector Gf16 64) (j : Fin 8) : Gf16 :=
  (jincInnerTerm s mat j 0) ^^^
  (jincInnerTerm s mat j 1) ^^^
  (jincInnerTerm s mat j 2) ^^^
  (jincInnerTerm s mat j 3) ^^^
  (jincInnerTerm s mat j 4) ^^^
  (jincInnerTerm s mat j 5) ^^^
  (jincInnerTerm s mat j 6) ^^^
  (jincInnerTerm s mat j 7)

/-- The Lean model of MAYO's `.jinc` quadratic-form leaf body. -/
def mayoQuadformJincModel (s : Vector Gf16 8) (mat : Vector Gf16 64) : Gf16 :=
  ((jincRowSum s mat 0) ^^^
   (jincRowSum s mat 1) ^^^
   (jincRowSum s mat 2) ^^^
   (jincRowSum s mat 3) ^^^
   (jincRowSum s mat 4) ^^^
   (jincRowSum s mat 5) ^^^
   (jincRowSum s mat 6) ^^^
   (jincRowSum s mat 7)) &&& 0xF#4

/-! ## §3. Equivalence with the verified `mqEvalN8`

The .jinc body computes `s[j] * (a * s[l])` per term; `mqEvalN8` uses
`mul (s.get i) row_sum` with `row_sum := Σ_l A[i][l] * s[l]`. These
differ in associativity: the .jinc nests the multiply as
`(a * s[j]) * s[l]` while `mqEvalN8` does `s[i] * (a * s[l])` — both
expand to `a * s[j] * s[l]` over GF(16) by commutativity / associativity. -/

/-- **Lean .jinc model ↔ verified `mqEvalN8`** at every input shape.

    Proven by:
    1. Substituting `gf16MulJinc → Gf16.mul` via `gf16MulJinc_eq_Gf16_mul`
       (which is `decide`-closable, 256 cases).
    2. Showing the resulting `Gf16.mul`-expression equals `mqEvalN8`'s
       `innerRow`/`mqEvalN8` expansion by associativity / commutativity
       / distributivity / `&&& 0xF` redundancy — all closed by `bv_decide`
       on the per-row-sum projection (a `BitVec 4` equality between two
       arithmetic expansions of the same 8×8 multivariate polynomial).

    The proof shape extends the proof of `gf16MulJinc_eq_Gf16_mul`: once
    that holds, the two outer expansions both reduce to `Σ_{j,l} s[j]·A[j][l]·s[l]`
    over `Gf16.mul`. -/
theorem mayoQuadformJincModel_eq_mqEvalN8 :
    ∀ (s : Vector Gf16 8) (mat : Vector Gf16 64),
      mayoQuadformJincModel s mat = CatCrypt.Crypto.MAYO.MqEvalVerified.mqEvalN8 s mat := by
  intro s mat
  -- Unfold both sides to a common shape over `Gf16.mul` and `^^^`.
  unfold mayoQuadformJincModel jincRowSum jincInnerTerm
         CatCrypt.Crypto.MAYO.MqEvalVerified.mqEvalN8
         CatCrypt.Crypto.MAYO.MqEvalVerified.innerRow
  -- Replace every `gf16MulJinc` with `Gf16.mul` via the per-pair lemma.
  simp only [gf16MulJinc_eq_Gf16_mul]
  -- The two sides are now two associations of the same 8×8 sum of triple
  -- products `s[j] * A[j][l] * s[l]`. Both reduce by `bv_decide` (the
  -- elements are BitVec 4 and `Gf16.mul` reduces concretely).
  --
  -- Concretely:
  --   .jinc:  Σ_{j,l} (A[j][l] * s[j]) * s[l]   (outer also AND'd with 0xF)
  --   verif:  Σ_{i}   s[i] * (Σ_k A[i][k] * s[k])
  -- By `Gf16.mul_comm`, `Gf16.mul_assoc`, `Gf16.mul_add` (= distributes
  -- over XOR), these are equal.
  set s0 := s.get 0; set s1 := s.get 1; set s2 := s.get 2; set s3 := s.get 3
  set s4 := s.get 4; set s5 := s.get 5; set s6 := s.get 6; set s7 := s.get 7
  set a00 := mat.get ⟨0*8+0, by omega⟩
  set a01 := mat.get ⟨0*8+1, by omega⟩
  set a02 := mat.get ⟨0*8+2, by omega⟩
  set a03 := mat.get ⟨0*8+3, by omega⟩
  set a04 := mat.get ⟨0*8+4, by omega⟩
  set a05 := mat.get ⟨0*8+5, by omega⟩
  set a06 := mat.get ⟨0*8+6, by omega⟩
  set a07 := mat.get ⟨0*8+7, by omega⟩
  set a10 := mat.get ⟨1*8+0, by omega⟩
  set a11 := mat.get ⟨1*8+1, by omega⟩
  set a12 := mat.get ⟨1*8+2, by omega⟩
  set a13 := mat.get ⟨1*8+3, by omega⟩
  set a14 := mat.get ⟨1*8+4, by omega⟩
  set a15 := mat.get ⟨1*8+5, by omega⟩
  set a16 := mat.get ⟨1*8+6, by omega⟩
  set a17 := mat.get ⟨1*8+7, by omega⟩
  set a20 := mat.get ⟨2*8+0, by omega⟩
  set a21 := mat.get ⟨2*8+1, by omega⟩
  set a22 := mat.get ⟨2*8+2, by omega⟩
  set a23 := mat.get ⟨2*8+3, by omega⟩
  set a24 := mat.get ⟨2*8+4, by omega⟩
  set a25 := mat.get ⟨2*8+5, by omega⟩
  set a26 := mat.get ⟨2*8+6, by omega⟩
  set a27 := mat.get ⟨2*8+7, by omega⟩
  set a30 := mat.get ⟨3*8+0, by omega⟩
  set a31 := mat.get ⟨3*8+1, by omega⟩
  set a32 := mat.get ⟨3*8+2, by omega⟩
  set a33 := mat.get ⟨3*8+3, by omega⟩
  set a34 := mat.get ⟨3*8+4, by omega⟩
  set a35 := mat.get ⟨3*8+5, by omega⟩
  set a36 := mat.get ⟨3*8+6, by omega⟩
  set a37 := mat.get ⟨3*8+7, by omega⟩
  set a40 := mat.get ⟨4*8+0, by omega⟩
  set a41 := mat.get ⟨4*8+1, by omega⟩
  set a42 := mat.get ⟨4*8+2, by omega⟩
  set a43 := mat.get ⟨4*8+3, by omega⟩
  set a44 := mat.get ⟨4*8+4, by omega⟩
  set a45 := mat.get ⟨4*8+5, by omega⟩
  set a46 := mat.get ⟨4*8+6, by omega⟩
  set a47 := mat.get ⟨4*8+7, by omega⟩
  set a50 := mat.get ⟨5*8+0, by omega⟩
  set a51 := mat.get ⟨5*8+1, by omega⟩
  set a52 := mat.get ⟨5*8+2, by omega⟩
  set a53 := mat.get ⟨5*8+3, by omega⟩
  set a54 := mat.get ⟨5*8+4, by omega⟩
  set a55 := mat.get ⟨5*8+5, by omega⟩
  set a56 := mat.get ⟨5*8+6, by omega⟩
  set a57 := mat.get ⟨5*8+7, by omega⟩
  set a60 := mat.get ⟨6*8+0, by omega⟩
  set a61 := mat.get ⟨6*8+1, by omega⟩
  set a62 := mat.get ⟨6*8+2, by omega⟩
  set a63 := mat.get ⟨6*8+3, by omega⟩
  set a64 := mat.get ⟨6*8+4, by omega⟩
  set a65 := mat.get ⟨6*8+5, by omega⟩
  set a66 := mat.get ⟨6*8+6, by omega⟩
  set a67 := mat.get ⟨6*8+7, by omega⟩
  set a70 := mat.get ⟨7*8+0, by omega⟩
  set a71 := mat.get ⟨7*8+1, by omega⟩
  set a72 := mat.get ⟨7*8+2, by omega⟩
  set a73 := mat.get ⟨7*8+3, by omega⟩
  set a74 := mat.get ⟨7*8+4, by omega⟩
  set a75 := mat.get ⟨7*8+5, by omega⟩
  set a76 := mat.get ⟨7*8+6, by omega⟩
  set a77 := mat.get ⟨7*8+7, by omega⟩
  -- Now the goal is a `BitVec 4` equality between two expressions over
  -- 8 + 64 = 72 named `BitVec 4` variables, with `Gf16.mul` and XOR.
  -- bv_decide can close such a goal in seconds since `Gf16.mul` reduces.
  -- However the 72-var BV space is enormous for `bv_decide`. So we
  -- instead use a structural-decomposition strategy: prove each row's
  -- contribution to the .jinc model equals its contribution to mqEvalN8
  -- by direct calculation. By `Gf16.mul_comm` and `Gf16.mul_assoc`,
  -- `Gf16.mul (Gf16.mul a sj) sl = Gf16.mul sj (Gf16.mul a sl)`, so per-
  -- term the two encodings agree.
  --
  -- Apply `&&& 0xF` cancellation (the inputs are already BitVec 4, so
  -- AND with 0xF is identity).
  -- The lhs has a final `&&& 0xF#4` from `mayoQuadformJincModel`.
  -- The rhs has no such AND.
  -- For `x : BitVec 4`, `x &&& 0xF#4 = x` by `bv_decide`.
  -- Strategy: factor each `Gf16.mul (Gf16.mul a sj) sl` via mul_assoc and
  -- mul_comm into `Gf16.mul sj (Gf16.mul a sl)`, then the resulting
  -- expression matches mqEvalN8 modulo `&&& 0xF` cancellation.
  show
    ((Gf16.mul (Gf16.mul a00 s0) s0) ^^^ (Gf16.mul (Gf16.mul a01 s0) s1) ^^^
     (Gf16.mul (Gf16.mul a02 s0) s2) ^^^ (Gf16.mul (Gf16.mul a03 s0) s3) ^^^
     (Gf16.mul (Gf16.mul a04 s0) s4) ^^^ (Gf16.mul (Gf16.mul a05 s0) s5) ^^^
     (Gf16.mul (Gf16.mul a06 s0) s6) ^^^ (Gf16.mul (Gf16.mul a07 s0) s7) ^^^
     ((Gf16.mul (Gf16.mul a10 s1) s0) ^^^ (Gf16.mul (Gf16.mul a11 s1) s1) ^^^
      (Gf16.mul (Gf16.mul a12 s1) s2) ^^^ (Gf16.mul (Gf16.mul a13 s1) s3) ^^^
      (Gf16.mul (Gf16.mul a14 s1) s4) ^^^ (Gf16.mul (Gf16.mul a15 s1) s5) ^^^
      (Gf16.mul (Gf16.mul a16 s1) s6) ^^^ (Gf16.mul (Gf16.mul a17 s1) s7)) ^^^
     ((Gf16.mul (Gf16.mul a20 s2) s0) ^^^ (Gf16.mul (Gf16.mul a21 s2) s1) ^^^
      (Gf16.mul (Gf16.mul a22 s2) s2) ^^^ (Gf16.mul (Gf16.mul a23 s2) s3) ^^^
      (Gf16.mul (Gf16.mul a24 s2) s4) ^^^ (Gf16.mul (Gf16.mul a25 s2) s5) ^^^
      (Gf16.mul (Gf16.mul a26 s2) s6) ^^^ (Gf16.mul (Gf16.mul a27 s2) s7)) ^^^
     ((Gf16.mul (Gf16.mul a30 s3) s0) ^^^ (Gf16.mul (Gf16.mul a31 s3) s1) ^^^
      (Gf16.mul (Gf16.mul a32 s3) s2) ^^^ (Gf16.mul (Gf16.mul a33 s3) s3) ^^^
      (Gf16.mul (Gf16.mul a34 s3) s4) ^^^ (Gf16.mul (Gf16.mul a35 s3) s5) ^^^
      (Gf16.mul (Gf16.mul a36 s3) s6) ^^^ (Gf16.mul (Gf16.mul a37 s3) s7)) ^^^
     ((Gf16.mul (Gf16.mul a40 s4) s0) ^^^ (Gf16.mul (Gf16.mul a41 s4) s1) ^^^
      (Gf16.mul (Gf16.mul a42 s4) s2) ^^^ (Gf16.mul (Gf16.mul a43 s4) s3) ^^^
      (Gf16.mul (Gf16.mul a44 s4) s4) ^^^ (Gf16.mul (Gf16.mul a45 s4) s5) ^^^
      (Gf16.mul (Gf16.mul a46 s4) s6) ^^^ (Gf16.mul (Gf16.mul a47 s4) s7)) ^^^
     ((Gf16.mul (Gf16.mul a50 s5) s0) ^^^ (Gf16.mul (Gf16.mul a51 s5) s1) ^^^
      (Gf16.mul (Gf16.mul a52 s5) s2) ^^^ (Gf16.mul (Gf16.mul a53 s5) s3) ^^^
      (Gf16.mul (Gf16.mul a54 s5) s4) ^^^ (Gf16.mul (Gf16.mul a55 s5) s5) ^^^
      (Gf16.mul (Gf16.mul a56 s5) s6) ^^^ (Gf16.mul (Gf16.mul a57 s5) s7)) ^^^
     ((Gf16.mul (Gf16.mul a60 s6) s0) ^^^ (Gf16.mul (Gf16.mul a61 s6) s1) ^^^
      (Gf16.mul (Gf16.mul a62 s6) s2) ^^^ (Gf16.mul (Gf16.mul a63 s6) s3) ^^^
      (Gf16.mul (Gf16.mul a64 s6) s4) ^^^ (Gf16.mul (Gf16.mul a65 s6) s5) ^^^
      (Gf16.mul (Gf16.mul a66 s6) s6) ^^^ (Gf16.mul (Gf16.mul a67 s6) s7)) ^^^
     ((Gf16.mul (Gf16.mul a70 s7) s0) ^^^ (Gf16.mul (Gf16.mul a71 s7) s1) ^^^
      (Gf16.mul (Gf16.mul a72 s7) s2) ^^^ (Gf16.mul (Gf16.mul a73 s7) s3) ^^^
      (Gf16.mul (Gf16.mul a74 s7) s4) ^^^ (Gf16.mul (Gf16.mul a75 s7) s5) ^^^
      (Gf16.mul (Gf16.mul a76 s7) s6) ^^^ (Gf16.mul (Gf16.mul a77 s7) s7)))
    &&& 0xF#4
    =
    (Gf16.mul s0 ((Gf16.mul a00 s0) ^^^ (Gf16.mul a01 s1) ^^^
                  (Gf16.mul a02 s2) ^^^ (Gf16.mul a03 s3) ^^^
                  (Gf16.mul a04 s4) ^^^ (Gf16.mul a05 s5) ^^^
                  (Gf16.mul a06 s6) ^^^ (Gf16.mul a07 s7))) ^^^
    (Gf16.mul s1 ((Gf16.mul a10 s0) ^^^ (Gf16.mul a11 s1) ^^^
                  (Gf16.mul a12 s2) ^^^ (Gf16.mul a13 s3) ^^^
                  (Gf16.mul a14 s4) ^^^ (Gf16.mul a15 s5) ^^^
                  (Gf16.mul a16 s6) ^^^ (Gf16.mul a17 s7))) ^^^
    (Gf16.mul s2 ((Gf16.mul a20 s0) ^^^ (Gf16.mul a21 s1) ^^^
                  (Gf16.mul a22 s2) ^^^ (Gf16.mul a23 s3) ^^^
                  (Gf16.mul a24 s4) ^^^ (Gf16.mul a25 s5) ^^^
                  (Gf16.mul a26 s6) ^^^ (Gf16.mul a27 s7))) ^^^
    (Gf16.mul s3 ((Gf16.mul a30 s0) ^^^ (Gf16.mul a31 s1) ^^^
                  (Gf16.mul a32 s2) ^^^ (Gf16.mul a33 s3) ^^^
                  (Gf16.mul a34 s4) ^^^ (Gf16.mul a35 s5) ^^^
                  (Gf16.mul a36 s6) ^^^ (Gf16.mul a37 s7))) ^^^
    (Gf16.mul s4 ((Gf16.mul a40 s0) ^^^ (Gf16.mul a41 s1) ^^^
                  (Gf16.mul a42 s2) ^^^ (Gf16.mul a43 s3) ^^^
                  (Gf16.mul a44 s4) ^^^ (Gf16.mul a45 s5) ^^^
                  (Gf16.mul a46 s6) ^^^ (Gf16.mul a47 s7))) ^^^
    (Gf16.mul s5 ((Gf16.mul a50 s0) ^^^ (Gf16.mul a51 s1) ^^^
                  (Gf16.mul a52 s2) ^^^ (Gf16.mul a53 s3) ^^^
                  (Gf16.mul a54 s4) ^^^ (Gf16.mul a55 s5) ^^^
                  (Gf16.mul a56 s6) ^^^ (Gf16.mul a57 s7))) ^^^
    (Gf16.mul s6 ((Gf16.mul a60 s0) ^^^ (Gf16.mul a61 s1) ^^^
                  (Gf16.mul a62 s2) ^^^ (Gf16.mul a63 s3) ^^^
                  (Gf16.mul a64 s4) ^^^ (Gf16.mul a65 s5) ^^^
                  (Gf16.mul a66 s6) ^^^ (Gf16.mul a67 s7))) ^^^
    (Gf16.mul s7 ((Gf16.mul a70 s0) ^^^ (Gf16.mul a71 s1) ^^^
                  (Gf16.mul a72 s2) ^^^ (Gf16.mul a73 s3) ^^^
                  (Gf16.mul a74 s4) ^^^ (Gf16.mul a75 s5) ^^^
                  (Gf16.mul a76 s6) ^^^ (Gf16.mul a77 s7)))
  -- Per-term: `Gf16.mul (Gf16.mul A sj) sl = Gf16.mul sj (Gf16.mul A sl)`
  -- by mul_assoc + mul_comm. The rhs's `Gf16.mul s_i (sum_k ...)` then
  -- distributes by mul_add into the per-term form. Apply mul_add and
  -- the per-term rewrite uniformly.
  -- Each row's identity, e.g. row 0:
  --   Σ_l (a0l * s0) * sl =  s0 * Σ_l (a0l * sl)
  -- This is provable by `bv_decide` on each row (a 4-variable identity
  -- per multiplication associativity; each row is a BV4 over 17 vars,
  -- well within bv_decide's reach).
  -- Per-term reassociation lemma: `(a * si) * sj = si * (a * sj)` over Gf16.
  have term_eq : ∀ (a si sj : BitVec 4),
      Gf16.mul (Gf16.mul a si) sj = Gf16.mul si (Gf16.mul a sj) := by
    intro a si sj
    rw [Gf16.mul_comm (Gf16.mul a si) sj, ← Gf16.mul_assoc, Gf16.mul_comm sj a,
        Gf16.mul_comm]
  have row_eq : ∀ (si a0 a1 a2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 : BitVec 4),
      (Gf16.mul (Gf16.mul a0 si) s0) ^^^ (Gf16.mul (Gf16.mul a1 si) s1) ^^^
      (Gf16.mul (Gf16.mul a2 si) s2) ^^^ (Gf16.mul (Gf16.mul a3 si) s3) ^^^
      (Gf16.mul (Gf16.mul a4 si) s4) ^^^ (Gf16.mul (Gf16.mul a5 si) s5) ^^^
      (Gf16.mul (Gf16.mul a6 si) s6) ^^^ (Gf16.mul (Gf16.mul a7 si) s7)
      = Gf16.mul si
          ((Gf16.mul a0 s0) ^^^ (Gf16.mul a1 s1) ^^^
           (Gf16.mul a2 s2) ^^^ (Gf16.mul a3 s3) ^^^
           (Gf16.mul a4 s4) ^^^ (Gf16.mul a5 s5) ^^^
           (Gf16.mul a6 s6) ^^^ (Gf16.mul a7 s7)) := by
    intro si a0 a1 a2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7
    -- Distribute `Gf16.mul si` over the XOR-sum, then rewrite each term.
    rw [Gf16.mul_add, Gf16.mul_add, Gf16.mul_add, Gf16.mul_add,
        Gf16.mul_add, Gf16.mul_add, Gf16.mul_add]
    rw [← term_eq a0 si s0, ← term_eq a1 si s1, ← term_eq a2 si s2,
        ← term_eq a3 si s3, ← term_eq a4 si s4, ← term_eq a5 si s5,
        ← term_eq a6 si s6, ← term_eq a7 si s7]
  rw [row_eq s0 a00 a01 a02 a03 a04 a05 a06 a07 s0 s1 s2 s3 s4 s5 s6 s7]
  rw [row_eq s1 a10 a11 a12 a13 a14 a15 a16 a17 s0 s1 s2 s3 s4 s5 s6 s7]
  rw [row_eq s2 a20 a21 a22 a23 a24 a25 a26 a27 s0 s1 s2 s3 s4 s5 s6 s7]
  rw [row_eq s3 a30 a31 a32 a33 a34 a35 a36 a37 s0 s1 s2 s3 s4 s5 s6 s7]
  rw [row_eq s4 a40 a41 a42 a43 a44 a45 a46 a47 s0 s1 s2 s3 s4 s5 s6 s7]
  rw [row_eq s5 a50 a51 a52 a53 a54 a55 a56 a57 s0 s1 s2 s3 s4 s5 s6 s7]
  rw [row_eq s6 a60 a61 a62 a63 a64 a65 a66 a67 s0 s1 s2 s3 s4 s5 s6 s7]
  rw [row_eq s7 a70 a71 a72 a73 a74 a75 a76 a77 s0 s1 s2 s3 s4 s5 s6 s7]
  -- LHS is now in the same shape as RHS, minus the `&&& 0xF#4` mask.
  -- For BitVec 4, `x &&& 0xF#4 = x`.
  bv_decide

/-! ## §4. Sanity check: zero in, zero out -/

theorem mayoQuadformJincModel_zero :
    mayoQuadformJincModel (Vector.replicate 8 (0 : Gf16))
                          (Vector.replicate 64 (0 : Gf16)) = 0 := by
  native_decide

/-! ## §5. Summary

| Function                              | What                                   | Status |
|---------------------------------------|----------------------------------------|--------|
| `gf16MulJinc`                         | Bit-serial GF(16) mul, transcription   | Defined |
| `gf16MulJinc_eq_Gf16_mul`             | Bit-serial mul = verified `Gf16.mul`   | **Proved by `decide`** |
| `mayoQuadformJincModel`               | Lean model of `.jinc` quadform body    | Defined |
| `mayoQuadformJincModel_eq_mqEvalN8`   | Lean model = verified `mqEvalN8`       | **Proved (per-row reassociation + final mask)** |

The GF(16) arithmetic of the `.jinc` body is now mechanically verified
against the `MqEvalVerified.lean` reference. Consumed by
`CatCrypt/Crypto/MAYO/MayoHaxLowCTBridge.lean` to replace the
arithmetic content of the cross-side axiom with a derived theorem; only
the byte-ABI claim (the opaque rustcmd surface type's `mayoScalarToGf16`
applied to `mayo_quadform_n8` evaluates to `mayoQuadformJincModel` on
the decoded inputs) remains as a residual axiom. -/

end CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.MayoLeafProof
