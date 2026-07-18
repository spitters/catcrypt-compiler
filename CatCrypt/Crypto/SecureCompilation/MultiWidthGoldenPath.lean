/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
import Std.Tactic.BVDecide

/-!
# Multi-width golden path: width-32 `Com jasminDialect` at the dialect level

The golden path (`FieldEmitGoldenPath.lean`) emits field-arithmetic kernels by
writing them ONCE as a `Com jasminDialect` over `.reg 64`, proving `Com.denote =
<spec>`, and letting `comToReg_faithful` (`ScalarLinDeBruijn.lean`) discharge the
backend lowering for free. Several real primitives — ChaCha20's quarter-round,
SHA-256's `Σ`/`σ`, ML-DSA's `reduce32` — are **32-bit**, so this file pushes the
width-32 frontier as far as the *current* architecture allows from a single
additive file (it edits no shared file).

## What is proven here (all genuine, non-vacuous, dialect-level)

The `jasminDialect` denotation is **width-generic**: `regArith bop w` acts over
`BitVec w` for any `w`, and `TyDenote (.reg w) = BitVec w`. So a width-32 `Com`
denotes to a genuine `BitVec 32` value. We build and prove:

* `add32` — `.regArith .add 32` over `[.reg 32, .reg 32]`; `Com.denote = a + b`
  (`BitVec 32`), by `rfl`.
* `xor32` — `.regArith .xor 32`; `Com.denote = a ^^^ b` (`BitVec 32`), by `rfl`.
* `rotr32 k` — the ChaCha20/SHA-256 right-rotate idiom `(a >>> k) ||| (a <<< (32-k))`
  built from `.shrImm 32 k`, `.shlImm 32 (32-k)`, `.regArith .or 32`;
  `Com.denote = a.rotateRight k` (`BitVec 32`) for the concrete amounts ChaCha20
  uses (`16, 12, 8, 7`), proven by `bv_decide` (an honest in-range bit identity,
  the width-32 instance of `JasminDialect.rorImm_denote_eq_shiftOr`).

These hold purely at the dialect denotation and are the genuine width-32 content
the architecture supports today.

## The documented gap: why the BACKEND emit stays width-64

`comToReg_faithful` does **not** carry a width-32 op, and this is not an
oversight that this file could patch from the outside — it is a property of the
*neutral `RegStmt` model* that all three backends (AArch64, RISC-V, x86) share.
The hardcoding is concentrated in `ScalarLinDeBruijn.lean`:

* `envOf` (the valuation→neutral-env reflection) only *places* `.reg 64`
  bindings (its second match arm is literally `(.reg 64) :: _`); a `.reg 32`
  binding falls through to the *drop* arm, so a width-32 valuation is not
  reflected into the register file at all.
* `AllReg64 Γ := ∀ t ∈ Γ, t = .reg 64` — the faithfulness theorem's context
  hypothesis is *definitionally* all-`reg 64`.
* `SupportedOp` pins every op to width 64 (`.regArith bop 64`, `.mulhi 64`,
  `.shrImm 64 k`, …), and `ComOK` is indexed at `(.reg 64)`.
* The neutral `RegStmt`/`Env` registers are `BitVec 64` (`Env = String → BitVec
  64`). A 64-bit register `add` does **not** equal a 32-bit wrapping add unless
  the inputs are known `< 2^32`: `(add32 a b)` wraps mod `2^32`, whereas the
  64-bit register would carry into bits 32..63.

This file makes that masking requirement *precise* and machine-checked rather
than hand-waved:

* `add32_zext_eq_mask` — `(add32 a b).zeroExtend 64 = ((a.zeroExtend 64) +
  (b.zeroExtend 64)) &&& 0xFFFFFFFF`, by `bv_decide`. The width-32 wrapping add,
  zero-extended into a 64-bit register, equals the 64-bit register add **masked
  to the low 32 bits**. So a faithful width-32 backend needs a `RegStmt` model
  whose registers carry a *width tag* (or an everywhere-`&&& 0xFFFFFFFF` masked
  semantics on 32-bit results), plus a `< 2^32` (or zero-extended) register
  invariant threaded through `envOf` / the op-correctness lemmas.

**What full width-32 emit needs** (a shared-file change, deliberately NOT done
here): generalise the neutral model from `Env = String → BitVec 64` to a
width-aware register file (or carry a per-name `< 2^width` invariant), restate
`SupportedOp`/`AllReg64`/`envOf`/`opToStmts_*_correct`/`comToReg_faithful` over a
generic `w` under that invariant, and emit the width-tagged register op on each
backend (`w` form of ARM/RISC-V/x86 add). `add32_zext_eq_mask` is the exact
obligation that generalisation must discharge per op. Until then, width-32 lives
at the dialect/`Com.denote` layer (proven below) and the backend emit is 64-bit.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MultiWidth

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. Width-32 source `Com`s over `[.reg 32, .reg 32]` -/

/-- **Width-32 add.** `v := a + b ; ret v` over args `[a, b] : [.reg 32, .reg 32]`.
    The width-32 instance of `FieldEmitGoldenPath.fieldAddCom`. -/
def add32 : Com jasminDialect [.reg 32, .reg 32] (.reg 32) :=
  .var { op := .regArith .add 32, retTy_eq := rfl,
         args := .cons .here (.cons (.there .here) .nil) }
    (.ret .here)

/-- **Width-32 xor.** `v := a ^^^ b ; ret v`. The ARX/SHA mixing op. -/
def xor32 : Com jasminDialect [.reg 32, .reg 32] (.reg 32) :=
  .var { op := .regArith .xor 32, retTy_eq := rfl,
         args := .cons .here (.cons (.there .here) .nil) }
    (.ret .here)

/-- **Width-32 right-rotate by `k`** as the portable shift-or idiom
    `(a >>> k) ||| (a <<< (32 - k))`, over arg `[a] : [.reg 32]`:

        hi := a >>> k         -- shrImm 32 k
        lo := a <<< (32 - k)  -- shlImm 32 (32 - k)
        r  := hi ||| lo       -- regArith .or 32
        ret r

    This is the rotate ChaCha20's quarter-round and SHA-256's `Σ`/`σ` spell. -/
def rotr32 (k : Nat) : Com jasminDialect [.reg 32] (.reg 32) :=
  .var { op := .shrImm 32 k, retTy_eq := rfl, args := .cons .here .nil }
  (.var { op := .shlImm 32 (32 - k), retTy_eq := rfl,
          args := .cons (.there .here) .nil }
  (.var { op := .regArith .or 32, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
    (.ret .here)))

/-! ## 2. Dialect-level denote/spec theorems (genuine `BitVec 32`)

`Com.denote` reduces structurally through the width-generic `jasminDenote`. -/

/-- **`add32` denotes the width-32 wrapping sum** `a + b : BitVec 32`, by `rfl`. -/
theorem add32_denote (a b : BitVec 32) :
    Com.denote add32 (.cons a (.cons b .nil)) = a + b := rfl

/-- **`xor32` denotes `a ^^^ b : BitVec 32`**, by `rfl`. -/
theorem xor32_denote (a b : BitVec 32) :
    Com.denote xor32 (.cons a (.cons b .nil)) = a ^^^ b := rfl

/-- **`rotr32 k` denotes the shift-or form** `(a >>> k) ||| (a <<< (32 - k))`, by
    `rfl` (structural reduction of the three-op chain). This is the raw idiom; the
    `= a.rotateRight k` characterisation is `rotr32_eq_rotateRight` below. -/
theorem rotr32_denote (k : Nat) (a : BitVec 32) :
    Com.denote (rotr32 k) (.cons a .nil) = (a >>> k) ||| (a <<< (32 - k)) := rfl

/-- **`rotr32 k` computes a genuine 32-bit right-rotate** for an in-range amount
    `0 < k < 32`: `Com.denote (rotr32 k) ⟨a⟩ = a.rotateRight k`. The width-32
    instance of `JasminDialect.rorImm_denote_eq_shiftOr` (the `BitVec` rotate law
    `rotateRight_def` specialised to `k % 32 = k`). -/
theorem rotr32_eq_rotateRight (k : Nat) (hk : k < 32) (a : BitVec 32) :
    Com.denote (rotr32 k) (.cons a .nil) = a.rotateRight k := by
  rw [rotr32_denote, BitVec.rotateRight_def, Nat.mod_eq_of_lt hk]

/-- **ChaCha20 quarter-round rotates, concretely.** The four amounts ChaCha20
    uses (`16, 12, 8, 7`) each denote the corresponding `BitVec 32` rotate, by
    `bv_decide` (a self-contained bit identity at the concrete amount). -/
theorem rotr32_chacha16 (a : BitVec 32) :
    Com.denote (rotr32 16) (.cons a .nil) = a.rotateRight 16 :=
  rotr32_eq_rotateRight 16 (by norm_num) a

theorem rotr32_chacha12 (a : BitVec 32) :
    Com.denote (rotr32 12) (.cons a .nil) = a.rotateRight 12 :=
  rotr32_eq_rotateRight 12 (by norm_num) a

theorem rotr32_chacha8 (a : BitVec 32) :
    Com.denote (rotr32 8) (.cons a .nil) = a.rotateRight 8 :=
  rotr32_eq_rotateRight 8 (by norm_num) a

theorem rotr32_chacha7 (a : BitVec 32) :
    Com.denote (rotr32 7) (.cons a .nil) = a.rotateRight 7 :=
  rotr32_eq_rotateRight 7 (by norm_num) a

/-! ## 3. The precise masking requirement the width-64 backend forces

The neutral `RegStmt`/`Env` register file is `BitVec 64`. A 64-bit register add
agrees with the width-32 `add32` only after masking to the low 32 bits — the
exact obligation a width-aware backend would have to discharge. -/

/-- **The masking requirement, machine-checked.** The width-32 wrapping sum
    `add32 a b`, zero-extended into a 64-bit register, equals the 64-bit register
    add of the zero-extended inputs **masked to the low 32 bits**:

        (add32 a b).zeroExtend 64
          = ((a.zeroExtend 64) + (b.zeroExtend 64)) &&& 0xFFFFFFFF.

    A 64-bit register `add` carries into bits 32..63; the width-32 op wraps mod
    `2^32`. They reconcile only under the `&&& 0xFFFFFFFF` mask. This is precisely
    what a faithful width-32 emit must add to the neutral `RegStmt` semantics
    (a width-tagged register file, or a masked-result invariant). -/
theorem add32_zext_eq_mask (a b : BitVec 32) :
    (Com.denote add32 (.cons a (.cons b .nil))).zeroExtend 64
      = (((a.zeroExtend 64) + (b.zeroExtend 64)) &&& (0xFFFFFFFF : BitVec 64)) := by
  rw [add32_denote]; bv_decide

/-- **The mask is genuinely load-bearing, not cosmetic.** The 64-bit register add
    of two zero-extended 32-bit values can carry into bit 32 (e.g. `a = b =
    2^32-1` gives `2^33 - 2`, with bit 32 set), so the unmasked 64-bit add does
    **not** in general equal the zero-extended width-32 result — the `&&&
    0xFFFFFFFF` in `add32_zext_eq_mask` cannot be dropped. This witnesses exactly
    why a width-32 backend cannot reuse the 64-bit register `add` verbatim: it
    must either mask every 32-bit result or thread a `< 2^32`-and-no-carry
    invariant (which a bare `add` does not preserve). -/
theorem add32_mask_necessary :
    ∃ a b : BitVec 32,
      (Com.denote add32 (.cons a (.cons b .nil))).zeroExtend 64
        ≠ ((a.zeroExtend 64) + (b.zeroExtend 64)) := by
  refine ⟨BitVec.allOnes 32, BitVec.allOnes 32, ?_⟩
  rw [add32_denote]; bv_decide

end CatCrypt.Crypto.SecureCompilation.MultiWidth
