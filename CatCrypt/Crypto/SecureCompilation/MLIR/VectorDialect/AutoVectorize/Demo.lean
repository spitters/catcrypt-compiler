/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.AutoVectorize.Vectorize

/-!
# Auto-Vectorize — Worked demo on the HMAC `K ⊕ pad` step (task #108)

A worked example wiring the auto-vectorize pass into a tiny inline crypto
kernel — the **HMAC `K ⊕ ipad` / `K ⊕ opad` XOR-pad**.

The XOR-pad is a 16-word independent XOR over `BitVec 32` (sometimes 16
`BitVec 64` words for `BLOCK = 128`). The existing emit
`Sha2Emit / HmacHkdfEmit.hmacXorPadJazz` puts down 16 inline jasmin
`regArith xor` instructions today. This is a textbook `lanewiseAdd`
pattern — N independent same-shape same-op binary ops — with the per-lane
operator instantiated as `BitVec.xor`.

## What this demo shows

1. The original scalar denotation: lane `i` computes `K[i] ^^^ pad[i]`,
   modelled as the `Fin 16 → BitVec 32` lane function.
2. The detected pattern: `VectorizablePattern.lanewiseAdd 16 (· ^^^ ·) K pad`
   (despite the constructor's name, `lanewiseAdd` carries an arbitrary
   binary `α → α → α` operator — the *shape* is "N independent binary
   ops", not "N additions specifically").
3. The vectorized op: `VectorOp.add (· ^^^ ·) K pad` (same comment about
   the constructor name).
4. The proven equivalence:
   `denoteVectorOp (vectorize pattern) = .vec (scalar XOR-pad)`.

This is a *worked example* — the demo does **not** rewrite
`HmacHkdfEmit.lean`; it only shows the equivalence on a freestanding model
of the kernel step. A Phase-2 rewrite would have to thread this through the
`Com`-level emit, which is a parallel-agent territory (the `Sha2*Emit`
files are reserved to the #179 agent).

## Why HMAC XOR-pad?

* It's small (16 lanes) so the demo theorem is `rfl`-class.
* It uses `BitVec` lanes (not opaque `α`), giving a concrete demonstration.
* The existing emit literally is 16 inline `xor`s — the canonical
  N-independent-binary-op shape the auto-vectorize pass exists to detect.
* No parallel-agent overlap: `HmacHkdfEmit.lean` is not in the
  do-not-touch list and this demo doesn't modify it anyway.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.AutoVectorize.Demo

open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect
open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.AutoVectorize

/-! ## 1. The kernel — HMAC XOR-pad

A SHA-256 HMAC block has 16 32-bit words. The `K ⊕ pad` step XORs every
word of the (zero-padded) key against the corresponding word of the
`ipad`/`opad` constant. -/

/-- An HMAC-SHA256 block: 16 32-bit words. -/
abbrev HmacWord := BitVec 32
abbrev HmacBlock := Fin 16 → HmacWord

/-- The HMAC `ipad` constant repeated across the block: every byte is `0x36`,
    every 32-bit word is `0x36363636`. -/
def ipad : HmacBlock := fun _ => 0x36363636

/-- The HMAC `opad` constant: every byte `0x5c`, every word `0x5c5c5c5c`. -/
def opad : HmacBlock := fun _ => 0x5c5c5c5c

/-- The scalar reference for the HMAC `K ⊕ pad` step: lane-wise XOR. This
    is what the 16 inline `regArith xor` instructions in
    `hmacXorPadJazz` compute, expressed as a `Fin 16 → BitVec 32`
    lane function. -/
def hmacXorPad_scalar (K pad : HmacBlock) : HmacBlock :=
  fun i => (K i) ^^^ (pad i)

/-! ## 2. The detected pattern + vectorized op -/

/-- The `VectorizablePattern` the auto-vectorize pass would emit for the
    HMAC XOR-pad. Despite the constructor name `lanewiseAdd`, the
    operator field is an arbitrary `α → α → α` — here instantiated to
    `BitVec.xor`. -/
def hmacXorPad_pattern (K pad : HmacBlock) : VectorizablePattern HmacWord :=
  .lanewiseAdd 16 (fun x y => x ^^^ y) K pad

/-- The vectorized `VectorOp` produced by `vectorize` on the detected
    pattern. -/
def hmacXorPad_vectorOp (K pad : HmacBlock) : VectorOp HmacWord 16 :=
  vectorize (hmacXorPad_pattern K pad)

/-- The vectorized op is exactly `VectorOp.add` (which is the carrier-
    polymorphic "pointwise binary op" constructor) applied to the
    XOR-as-binary-op and the two input blocks. -/
theorem hmacXorPad_vectorOp_eq_add (K pad : HmacBlock) :
    hmacXorPad_vectorOp K pad
      = .add (fun x y => x ^^^ y) K pad := rfl

/-! ## 3. The equivalence theorem (the proven demo keystone) -/

/-- **Worked equivalence.** The vectorized HMAC XOR-pad denotes to exactly
    the scalar reference: the abstract `VectorOp.add` (with `BitVec.xor`
    as the per-lane operator) over the two 16-lane blocks computes the
    16 independent XORs that the scalar `hmacXorPad_scalar` does.

    Proof: a direct instance of `lanewiseAdd_vectorize_denotation_preserves`
    at `α = BitVec 32`, `op = (· ^^^ ·)`, `n = 16`. The `rfl` at the end is
    the lane-by-lane reduction (`VectorTy.map₂` agrees lane-wise with the
    scalar `fun i => K i ^^^ pad i`). -/
theorem hmacXorPad_vectorize_correct (K pad : HmacBlock) :
    denoteVectorOp (hmacXorPad_vectorOp K pad)
      = VectorOp.Result.vec (hmacXorPad_scalar K pad) := by
  -- Reduce to the keystone proof.
  have h := lanewiseAdd_vectorize_denotation_preserves
              16 (fun x y => x ^^^ y) K pad
  -- `h` reduces both sides; the only remaining gap is the definitional
  -- equality between `scalarDenote (lanewiseAdd …)` and
  -- `hmacXorPad_scalar`, which is `rfl`.
  exact h

/-! ## 4. The two concrete callers — `K ⊕ ipad` and `K ⊕ opad`

The HMAC construction calls the XOR-pad twice — once with `ipad`, once with
`opad`. Each instance is a concrete specialisation of `hmacXorPad_*`. -/

/-- The vectorized `K ⊕ ipad` step. -/
def kXorIpad_vectorOp (K : HmacBlock) : VectorOp HmacWord 16 :=
  hmacXorPad_vectorOp K ipad

/-- The vectorized `K ⊕ opad` step. -/
def kXorOpad_vectorOp (K : HmacBlock) : VectorOp HmacWord 16 :=
  hmacXorPad_vectorOp K opad

/-- Both HMAC pad steps preserve denotation under vectorization. -/
theorem kXorIpad_vectorize_correct (K : HmacBlock) :
    denoteVectorOp (kXorIpad_vectorOp K)
      = VectorOp.Result.vec (hmacXorPad_scalar K ipad) :=
  hmacXorPad_vectorize_correct K ipad

theorem kXorOpad_vectorize_correct (K : HmacBlock) :
    denoteVectorOp (kXorOpad_vectorOp K)
      = VectorOp.Result.vec (hmacXorPad_scalar K opad) :=
  hmacXorPad_vectorize_correct K opad

/-! ## 5. Conclusion

If a Phase-2 rewrite replaces the 16 inline `regArith xor` instructions in
`HmacHkdfEmit.hmacXorPadJazz` with a single
`VectorOp.add (· ^^^ ·) K ipad`-shaped op (then lowered back to the same
16 scalar XORs by `Lowering.lower`), then:

* `hmacXorPad_vectorize_correct` proves the rewrite preserves the
  cryptographic meaning (the XOR-pad is the same function);
* `denoteVectorOp_eq_lower_add` in `Lowering.lean` would prove that the
  Phase-2 lowering of the `VectorOp.add` back into per-lane scalar XORs
  matches the abstract denotation — which is exactly the chain the verified
  pipeline needs.

The existing HMAC reduction theorems in `HmacHkdfEmit.lean` then carry
through unchanged because the *meaning* of the XOR-pad does not change.
This is the same expressivity argument `ConsumerDemo.lean` makes for the
ChaCha 4-way `#VPADD_4u32` step, transposed onto the auto-vectorize
direction (scalar→vector) rather than the lowering direction
(vector→scalar). -/

end CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.AutoVectorize.Demo
