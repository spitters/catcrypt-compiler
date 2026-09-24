/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.FieldExpChainSemantics
public import CatCrypt.Crypto.Jasmin.Ed25519.CompressEmit

/-!
# `ed25519_compress` — chain-to-spec correctness

`CompressEmit.lean` emits a hand-authored `LowCT` for the Ed25519 point
compression `(X, Y, Z, T) → 32 bytes`.  The emit's `fe25519_invert_slot`
leaf is currently a single externally-implemented call; the *intent* is
that it implements the Bernstein 254S+11M addition chain
(`FieldExpChain.bernsteinInvChain`).

This file bridges the verified chain *data* to a **spec-level**
reference compress over `Fp25519 := ZMod curve25519Prime`:

```
compress_spec (X, Y, Z, T):
  let invZ = Z^(p − 2)              -- Fermat inversion
  let y_aff = Y * invZ
  let x_aff = X * invZ
  packSign y_aff x_aff              -- 32-byte encoding with sign bit
```

and an equivalent chain-based compress:

```
compressFromChain blocks (X, Y, Z, T):
  let invZ = applyChain blocks Z    -- runs the addition chain
  let y_aff = Y * invZ
  let x_aff = X * invZ
  packSign y_aff x_aff
```

The main theorem `compress_emit_correct` shows the two agree when the
chain is `bernsteinInvChain`, by reducing `applyChain bernsteinInvChain Z`
to `Z^(p − 2)` via `bernsteinInvChain_eq_pow_p_minus_2`.

## What is and isn't proved here

* **Proved**: `compressFromChain bernsteinInvChain xyzt = compress_spec xyzt`.
  This is the *algebraic* correctness of the chain emit: if the
  `fe25519_invert_slot` leaf in the emitted `LowCT` faithfully
  implements `applyChain bernsteinInvChain`, then the emit computes the
  reference compress.
* **Deferred**: the `LowCT`-level semantic equivalence
  `denote ed25519_compress_cmd = compress_spec`.  This requires:
  * a `denote : LowCT → State → State` (bedrock2 style), and
  * a `denote`-level specification of each leaf primitive
    (`fe25519_invert_slot`, `fe25519_mul_slot`, `xyzt_slot_*`,
    `fe25519_pack_sign`).

  The 6 leaf primitives are implemented by a small Rust shim in
  `bench/dalek/src/compress_leaves.rs` that delegates to dalek's verified
  field-element code path; their `denote`-level specs are the canonical
  pieces that, together with the structural decomposition in
  `ed25519_compress_cmd`, would close the full chain.  We capture the
  decomposition as a *structural lemma* (`compress_emit_structure`).

Byte-for-byte difftesting against `dalek_compress` (running on 80/80 RFC
vectors via `bench/dalek/src/compress_difftest.rs`) is the empirical
witness for the piece this module does not prove.

## References

* `FieldExpChain.bernsteinInvChain` — the verified addition-chain data.
* `FieldExpChainSemantics.bernsteinInvChain_eq_pow_p_minus_2` —
  the algebraic correctness of the chain.
* `InvP25519Algo.zmod_pow_p_sub_two_eq_inv` — Fermat's little theorem.
-/

@[expose] public section

set_option autoImplicit false

/-! ## §0  Structural helpers in `CompressEmit` namespace

`callCount` / `callNames` are placed in the `CompressEmit` namespace
(via namespace reopen) so the shape lemmas below can refer to them via
`CompressEmit.callCount` / `CompressEmit.callNames` without touching
`CompressEmit.lean` itself (owned by a different track). -/

namespace CatCrypt.Crypto.Jasmin.Ed25519.CompressEmit

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.LowCT

/-- Number of `RCall` nodes in a `LowCT`. -/
def callCount : LowCT → Nat
  | .RSkip => 0
  | .RSeq c1 c2 => callCount c1 + callCount c2
  | .RBlock body => callCount body
  | .RLetZero _ _ body => callCount body
  | .RCall _ _ _ => 1
  | _ => 0

/-- Names of the `RCall`s in a `LowCT`, in order. -/
def callNames : LowCT → List String
  | .RSkip => []
  | .RSeq c1 c2 => callNames c1 ++ callNames c2
  | .RBlock body => callNames body
  | .RLetZero _ _ body => callNames body
  | .RCall name _ _ => [name]
  | _ => []

end CatCrypt.Crypto.Jasmin.Ed25519.CompressEmit

namespace CatCrypt.Crypto.Jasmin.Ed25519.CompressEmitCorrect

open CatCrypt.Crypto.SecureCompilation.VIR.FieldExpChain
open CatCrypt.Crypto.Jasmin.Ed25519.InvP25519Algo

/-! ## §1  Spec-level field, sign bit, and pack -/

/-- Spec-level field: `Fp25519 := ZMod (2^255 − 19)`. -/
abbrev Fp25519 : Type := ZMod p25519

/-- The "y-encode" half of `fe25519_pack_sign`: encode a field element
    as a 32-byte little-endian sequence (we leave it as a parameter
    since byte encoding is a pure function and the chain correctness
    doesn't depend on its details). -/
def encodeFp25519 : Fp25519 → Vector UInt8 32 :=
  -- Standard little-endian encoding via the canonical lift to ℕ < p.
  -- We pin the spec to the `ZMod.val`-based encoding for definiteness.
  fun y =>
    Vector.ofFn fun (i : Fin 32) =>
      (UInt8.ofNat ((y.val >>> (8 * i.val)) &&& 0xff))

/-- The sign bit of a field element: the parity of its canonical lift.
    Matches dalek's `is_negative` (LSB of the 32-byte little-endian
    encoding). -/
def signBit (x : Fp25519) : Bool := x.val % 2 = 1

/-- Set bit 255 (= MSB of byte 31) of a 32-byte vector to `b`. -/
def setSignBit (bytes : Vector UInt8 32) (b : Bool) : Vector UInt8 32 :=
  let b31 := bytes[31]
  let b31' := if b then b31 ||| 0x80 else b31 &&& 0x7f
  bytes.set 31 b31'

/-- Pack `y_aff` with the sign bit of `x_aff` ORed into bit 255.
    This is the spec-level model of `fe25519_pack_sign`. -/
def packSign (y_aff x_aff : Fp25519) : Vector UInt8 32 :=
  setSignBit (encodeFp25519 y_aff) (signBit x_aff)

/-! ## §2  Reference spec: `compress_spec`

The compress operation `(X, Y, Z, T) → 32 bytes` over the abstract
field.  This is the *reference* — not the efficient computation. -/

/-- **Reference compress**: dehomogenise `(X : Y : Z : T)` to affine
    `(x, y)` via Fermat inversion, then pack `y` with the parity of `x`
    as the sign bit. -/
def compress_spec : Fp25519 × Fp25519 × Fp25519 × Fp25519 → Vector UInt8 32 :=
  fun ⟨X, Y, Z, _T⟩ =>
    let invZ := Z^(p25519 - 2)
    let y_aff := Y * invZ
    let x_aff := X * invZ
    packSign y_aff x_aff

/-! ## §3  Chain-based compress

Same compress, but with the Fermat inversion routed through
`applyChain : List Block → Fp25519 → Fp25519`. -/

/-- Compress an Edwards XYZT point using an addition chain for the
    inversion `Z → Z⁻¹`. -/
def compressFromChain (blocks : List Block) :
    Fp25519 × Fp25519 × Fp25519 × Fp25519 → Vector UInt8 32 :=
  fun ⟨X, Y, Z, _T⟩ =>
    let invZ := applyChain blocks Z
    let y_aff := Y * invZ
    let x_aff := X * invZ
    packSign y_aff x_aff

/-! ## §4  Main theorem: chain compress = spec compress

For Bernstein's chain, `applyChain bernsteinInvChain Z = Z^(p − 2)`
(proved in `FieldExpChainSemantics`), so the chain-based compress equals
the spec. -/

/-- **`compress_emit_correct`** (algebraic level).

The chain-based compress with the Bernstein 254S+11M inversion chain
equals the reference Fermat-inversion compress on every Edwards XYZT
point. -/
theorem compress_emit_correct
    (xyzt : Fp25519 × Fp25519 × Fp25519 × Fp25519) :
    compressFromChain bernsteinInvChain xyzt = compress_spec xyzt := by
  obtain ⟨X, Y, Z, T⟩ := xyzt
  simp only [compressFromChain, compress_spec, bernsteinInvChain_eq_pow_p_minus_2]

/-! ## §5  Structural correspondence with the `LowCT` emit

`ed25519_compress_cmd` (in `CompressEmit.lean`) is a hand-authored
sequence of 7 leaf calls:
```
xyzt_slot_x         (x_slot, xyzt)
xyzt_slot_y         (y_slot, xyzt)
xyzt_slot_z         (z_slot, xyzt)
fe25519_invert_slot (z_inv,  z_slot)
fe25519_mul_slot    (y_aff,  y_slot, z_inv)
fe25519_mul_slot    (x_aff,  x_slot, z_inv)
fe25519_pack_sign   (out,    y_aff,  x_aff)
```
This shape **structurally mirrors** `compressFromChain`:
* `xyzt_slot_{x,y,z}` extract `X`, `Y`, `Z` from the 200-byte XYZT
  buffer.
* `fe25519_invert_slot` is to be replaced by the Bernstein chain.
* The two `fe25519_mul_slot` calls compute `Y * invZ` and `X * invZ`.
* `fe25519_pack_sign` performs `packSign y_aff x_aff`.

Full denotational equivalence
`denote ed25519_compress_cmd = compress_spec` is **deferred** — it
requires a `denote : LowCT → State → State` plus a spec of each
leaf primitive.  The leaves are tested empirically (80/80 dalek
difftest vectors).

To make the structural claim machine-checkable we record the
*length* and *call sequence* of the emit and verify it matches the
chain compress decomposition. -/

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.LowCT

/-- **Shape lemma (structural)**: the emit's `RCall` sequence is exactly
    the 7-call decomposition that matches `compressFromChain`.

    This is a `decide`-able structural fact; it does not establish
    semantic equivalence (which requires a `denote` we do not yet have)
    but it locks in the call-graph shape so any future refactor that
    drops or reorders a leaf is caught at type-check time. -/
theorem compress_emit_structure :
    CompressEmit.callNames CompressEmit.ed25519_compress_cmd =
      [ "xyzt_slot_x", "xyzt_slot_y", "xyzt_slot_z",
        "fe25519_invert_slot",
        "fe25519_mul_slot", "fe25519_mul_slot",
        "fe25519_pack_sign" ] := by
  rfl

/-- `decide`-level structural fact: the emit has exactly 7 leaf calls. -/
theorem compress_emit_call_count :
    CompressEmit.callCount CompressEmit.ed25519_compress_cmd = 7 := by
  rfl

end CatCrypt.Crypto.Jasmin.Ed25519.CompressEmitCorrect
