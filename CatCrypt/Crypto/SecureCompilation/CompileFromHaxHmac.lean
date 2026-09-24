/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.CompileFromHax
public import CatCrypt.Crypto.SecureCompilation.CompileFromHax

/-!
# The verified compiler emits the HMAC/HKDF scalar bodies from extracted source

This module applies the verified compile-from-hax front to the
**HMAC/HKDF** scalar-bitwise loop/array bodies that `HmacHkdfEmit.lean`
authors *by hand* as `Com jasminDialect` terms. Each of those bodies is pure
scalar ALU (XOR / wrapping-add / OR) over the register width, so it is squarely in
the front's scalar fragment — exactly the `recogBin` family the SHA-256
(`CompileFromHaxLeaves`) and BLAKE2 (`CompileFromHaxBlake2`) leaves already drive.
Here we re-derive those bodies *through* `compileFromHax`, so the emitted jasmin
`Com` is **computed by the verified compiler from the extracted source**, with no
front change.

## In-scope bodies (from `HmacHkdfEmit.lean`)

* **`xorPadCom`** (`§2` of `HmacHkdfEmit`) — the HMAC `K ⊕ ipad` / `K ⊕ opad`
  pad. Its result slot denotes `K[15] ⊕ pad` (`xorPadCom_denote`). One
  `regArith xor` per block word; the result is a single `BitXor`. We model a
  representative **4-word slice** `xorPad4` (the full pad is `blockWords = 16`
  independent copies of the *same* one-word `out[j] = K[j] ^ pad` shape; the
  result var is `K[3] ^ pad` here, `K[15] ^ pad` in the 16-word original — the
  identical word-level fact, just at index 3 vs 15).
* **`xorPadComW`** (`§6`) — the width-generic XOR-pad (HMAC-SHA512/384 at
  `w = 64`). Same shape at width 64; `xorPad4W64` re-derives the `K[3] ⊕ pad`
  slice at `w = 64`.
* **`expandSkelBody`** (`§4a`) — the leaf-free wide-register HKDF-Expand
  T-chaining skeleton, a three-op `regArith` chain
  `v0 = T + T; v1 = v0 ^ T; v2 = v1 | v0`, returning `v2 = ((T+T)^T) | (T+T)`.
  Pure `add`/`xor`/`or`. We re-derive it at a representative scalar width
  `w = 32` (the original packs `8·hw = reg 256`; the body is width-uniform, so a
  scalar slice exercises the identical `add`/`xor`/`or` recognizer chain).

## Out of scope (leaf-linking)

* **`expandLeafBody`** (`§4b`) — its single binder is an `extCall`
  `hkdf_expand_step` to an *opaque* leaf (the dialect has no in-body immediate
  op to synthesise the per-iteration counter byte). An `extCall` is **not** in
  the front's scalar ALU fragment — it is a leaf-link (`CompileFromHaxLink`),
  not a body the compiler emits.

## Method (mirrors `CompileFromHaxLeaves` / `CompileFromHaxBlake2`)

Each in-scope body follows the per-primitive obligation pattern exactly:

1. A let-normalized `ImpExpr` source (`*Src`), one operator per `letBind`.
2. A source-spec lemma (`*_denoteScalar`) proving the source `denoteScalar`
   computes the body's closed form — the **same** RHS the hand-authored
   `*_denote` lemma in `HmacHkdfEmit.lean` targets.
3. A `*_isSome` lemma (`native_decide`): the compile succeeds.
4. The leaf theorem (`*_compiles`): the emitted jasmin `Com` denotes to that
   closed form, routed through the obligation `compileFromHax_meets_spec`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxHmac

open _root_.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## §1  The HMAC XOR-pad slice (`xorPadCom`, `w = 32`)

`HmacHkdfEmit.xorPadCom` emits `out[j] = K[j] ^ pad` for the 16 block words and
returns the last (`xorPadCom_denote : … = K[15] ⊕ pad`). Every word is the same
one-`BitXor` shape, so we model a **4-word slice** `xorPad4` whose result slot is
`K[3] ⊕ pad` — the identical word-level fact at index 3. Parameters
`["k0","k1","k2","k3","pad"]` (`nIn = 5`; `I 0..3 = K[0..3]`, `I 4 = pad`). -/

/-- The 4-word XOR-pad slice as a hax `ImpExpr`, fully let-normalized: one
    `BitXor` per key word against the shared `pad`, returning the last. Mirrors
    `HmacHkdfEmit.xorPadCom`'s `out[j] = K[j] ^ pad` shape (`blockWords` copies of
    this single-`BitXor` body; result var = the last word). -/
def xorPad4Src : ImpExpr :=
  .letBind "o0" (.app "BitXor" [.var "k0", .var "pad"])
   (.letBind "o1" (.app "BitXor" [.var "k1", .var "pad"])
    (.letBind "o2" (.app "BitXor" [.var "k2", .var "pad"])
     (.letBind "o3" (.app "BitXor" [.var "k3", .var "pad"])
      (.var "o3"))))

/-- The XOR-pad slice denotes (under `denoteScalar`) to `K[3] ⊕ pad` — exactly the
    word-level meaning `HmacHkdfEmit.xorPadCom_denote` records (`K[15] ⊕ pad` at the
    16-word index; `K[3] ⊕ pad` for this 4-word slice). -/
theorem xorPad4Src_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 32) :
    ImpExpr.denoteScalar ["k0", "k1", "k2", "k3", "pad"] I xorPad4Src (fun _ => none)
      = some (inpGet I 3 ^^^ inpGet I 4) := by
  rfl

/-- The compile-from-hax pipeline succeeds on the XOR-pad slice (`w = 32`,
    5 parameters). -/
theorem xorPad4_compileFromHax_isSome :
    (compileFromHax (w := 32) (nIn := 5) ["k0", "k1", "k2", "k3", "pad"] xorPad4Src).isSome := by
  native_decide

/-- **HMAC XOR-pad slice emitted by the verified compiler.** There is a compiled
    `Com jasminDialect` `c` with
    `compileFromHax ["k0","k1","k2","k3","pad"] xorPad4Src = some c`, and for every
    `(k0,k1,k2,k3,pad)`, `c`'s `BitVec 32` denotation is exactly `K[3] ⊕ pad` —
    the word-level pad fact `HmacHkdfEmit.xorPadCom_denote` records, emitted by
    the compiler from extracted source rather than hand-authored. Routed through
    the obligation `compileFromHax_meets_spec`. -/
theorem xorPad4_compiles :
    ∃ (c : Com jasminDialect (frontCtxt 32 5 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 5) ["k0", "k1", "k2", "k3", "pad"] xorPad4Src = some c ∧
      ∀ (k0 k1 k2 k3 pad : BitVec 32),
        c.denote (inputValuation 32 5 ![k0, k1, k2, k3, pad])
          = k3 ^^^ pad := by
  set c := (compileFromHax (w := 32) (nIn := 5) ["k0", "k1", "k2", "k3", "pad"] xorPad4Src).get
    xorPad4_compileFromHax_isSome with hc_def
  have hc : compileFromHax (w := 32) (nIn := 5) ["k0", "k1", "k2", "k3", "pad"] xorPad4Src
      = some c := (Option.some_get _).symm
  refine ⟨c, hc, ?_⟩
  intro k0 k1 k2 k3 pad
  have hspec : ImpExpr.denoteScalar ["k0", "k1", "k2", "k3", "pad"] ![k0, k1, k2, k3, pad]
      xorPad4Src (fun _ => none) = some (k3 ^^^ pad) := by
    have h := xorPad4Src_denoteScalar (nIn := 5) ![k0, k1, k2, k3, pad]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using! h
  exact compileFromHax_meets_spec (w := 32) (nIn := 5) ["k0", "k1", "k2", "k3", "pad"]
    ![k0, k1, k2, k3, pad] xorPad4Src _ hc hspec

/-! ## §2  The width-generic XOR-pad slice at `w = 64` (`xorPadComW`)

`HmacHkdfEmit.xorPadComW w` is the width-parameterized pad (HMAC-SHA512/384 use
`w = 64`); `xorPadComW_denote` records `K[15] ⊕ pad` at width `w`. We re-derive the
same `K[3] ⊕ pad` slice at `w = 64` — the only delta from `§1` is the register
width, the same `BitXor` recognizer chain. -/

/-- The 4-word XOR-pad slice source (shared with `§1`; width is fixed at the
    compile call, the source is width-agnostic). -/
theorem xorPad4Src_denoteScalar64 {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar ["k0", "k1", "k2", "k3", "pad"] I xorPad4Src (fun _ => none)
      = some (inpGet I 3 ^^^ inpGet I 4) := by
  rfl

/-- The compile-from-hax pipeline succeeds on the XOR-pad slice at `w = 64`. -/
theorem xorPad4W64_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 5) ["k0", "k1", "k2", "k3", "pad"] xorPad4Src).isSome := by
  native_decide

/-- **Width-64 HMAC XOR-pad slice emitted by the verified compiler.** The same
    `K[3] ⊕ pad` slice as `§1`, at `w = 64` — the width HMAC-SHA512/384 use
    over the 128-byte / 16-`u64` block. Re-derives `HmacHkdfEmit.xorPadComW_denote`'s
    word-level fact at width 64 through the compiler. Routed through
    `compileFromHax_meets_spec`. -/
theorem xorPad4W64_compiles :
    ∃ (c : Com jasminDialect (frontCtxt 64 5 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 5) ["k0", "k1", "k2", "k3", "pad"] xorPad4Src = some c ∧
      ∀ (k0 k1 k2 k3 pad : BitVec 64),
        c.denote (inputValuation 64 5 ![k0, k1, k2, k3, pad])
          = k3 ^^^ pad := by
  set c := (compileFromHax (w := 64) (nIn := 5) ["k0", "k1", "k2", "k3", "pad"] xorPad4Src).get
    xorPad4W64_compileFromHax_isSome with hc_def
  have hc : compileFromHax (w := 64) (nIn := 5) ["k0", "k1", "k2", "k3", "pad"] xorPad4Src
      = some c := (Option.some_get _).symm
  refine ⟨c, hc, ?_⟩
  intro k0 k1 k2 k3 pad
  have hspec : ImpExpr.denoteScalar ["k0", "k1", "k2", "k3", "pad"] ![k0, k1, k2, k3, pad]
      xorPad4Src (fun _ => none) = some (k3 ^^^ pad) := by
    have h := xorPad4Src_denoteScalar64 (nIn := 5) ![k0, k1, k2, k3, pad]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using! h
  exact compileFromHax_meets_spec (w := 64) (nIn := 5) ["k0", "k1", "k2", "k3", "pad"]
    ![k0, k1, k2, k3, pad] xorPad4Src _ hc hspec

/-! ## §3  The HKDF-Expand T-chaining skeleton body (`expandSkelBody`, `w = 32`)

`HmacHkdfEmit.expandSkelBody` is the leaf-free wide-register T-chaining skeleton:
the three-op `regArith` chain `v0 = T + T; v1 = v0 ^ T; v2 = v1 | v0`, returning
`v2 = ((T+T) ^ T) | (T+T)`. Pure `add`/`xor`/`or` over the accumulator. The
original packs `reg (8·hw) = reg 256`; the body is width-uniform, so we re-derive
the identical recognizer chain at a representative scalar width `w = 32`, single
parameter `["t"]`. -/

/-- The HKDF-Expand skeleton body as a hax `ImpExpr`, fully let-normalized:
    `v0 = wrapping_add(t, t); v1 = BitXor(v0, t); v2 = BitOr(v1, v0)`, returning
    `v2`. Mirrors `HmacHkdfEmit.expandSkelBody`'s `add`/`xor`/`or` chain. -/
def expandSkelSrc : ImpExpr :=
  .letBind "v0" (.app "wrapping_add" [.var "t", .var "t"])
   (.letBind "v1" (.app "BitXor" [.var "v0", .var "t"])
    (.letBind "v2" (.app "BitOr" [.var "v1", .var "v0"])
     (.var "v2")))

/-- The skeleton body's explicit closed form `((T+T) ^ T) | (T+T)` — the value
    `HmacHkdfEmit.expandSkelBody` computes from its accumulator `T`. -/
def expandSkelSpec (t : BitVec 32) : BitVec 32 :=
  let v0 := t + t
  let v1 := v0 ^^^ t
  let v2 := v1 ||| v0
  v2

/-- The skeleton body denotes (under `denoteScalar`) to `((T+T) ^ T) | (T+T)` —
    the closed form of `HmacHkdfEmit.expandSkelBody`'s three-op chain. -/
theorem expandSkelSrc_denoteScalar (I : Fin 1 → BitVec 32) :
    ImpExpr.denoteScalar ["t"] I expandSkelSrc (fun _ => none)
      = some (expandSkelSpec (I 0)) := by
  rfl

/-- The compile-from-hax pipeline succeeds on the skeleton body (`w = 32`, one
    parameter). -/
theorem expandSkel_compileFromHax_isSome :
    (compileFromHax (w := 32) (nIn := 1) ["t"] expandSkelSrc).isSome := by
  native_decide

/-- **HKDF-Expand T-chaining skeleton body emitted by the verified compiler.**
    There is a compiled `Com jasminDialect` `c` with
    `compileFromHax ["t"] expandSkelSrc = some c`, and for every `t`, `c`'s
    `BitVec 32` denotation is exactly `((t+t) ^ t) | (t+t)` — the closed form of
    `HmacHkdfEmit.expandSkelBody`'s three-op `regArith` chain, emitted by the
    compiler from extracted source rather than hand-authored. Routed through the
    obligation `compileFromHax_meets_spec`. -/
theorem expandSkel_compiles :
    ∃ (c : Com jasminDialect (frontCtxt 32 1 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 1) ["t"] expandSkelSrc = some c ∧
      ∀ (t : BitVec 32),
        c.denote (inputValuation 32 1 (fun _ => t))
          = ((t + t) ^^^ t) ||| (t + t) := by
  set c := (compileFromHax (w := 32) (nIn := 1) ["t"] expandSkelSrc).get
    expandSkel_compileFromHax_isSome with hc_def
  have hc : compileFromHax (w := 32) (nIn := 1) ["t"] expandSkelSrc = some c :=
    (Option.some_get _).symm
  refine ⟨c, hc, ?_⟩
  intro t
  have hspec := expandSkelSrc_denoteScalar (fun _ => t)
  exact compileFromHax_meets_spec (w := 32) (nIn := 1) ["t"] (fun _ => t)
    expandSkelSrc _ hc hspec

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxHmac
