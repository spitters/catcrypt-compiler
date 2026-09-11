/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxChaCha
public import CatCrypt.Crypto.Jasmin.ChaCha20QR

/-!
# #607 Phase 3b: functional tie — verified-compiler ChaCha20 quarter-round = protocol's abstract QR

This module wires the committed **compile-from-hax ChaCha20 quarter-round leaf**
(`CompileFromHaxChaCha.qr{A,B,C,D}_compiles`) into the abstract quarter-round
function that the ChaCha20 PRF security assumption quantifies over
(`CatCrypt.Crypto.Jasmin.ChaCha20QR.quarterRound`).

## What this is — and what it is NOT (honest framing)

This is a **functional-equality** tie, not a security claim.

- The compile-from-hax leaf proves a *functional-correctness* fact: the artifact
  emitted by the verified compiler computes the closed-form quarter-round
  reference `ThirToComFront.chachaQRSpec`
  (`qrA_compiles : … ∧ prog.denote … = (chachaQRSpec a b c d).1`, etc.).
- The ChaCha20 AEAD / PRF security lives elsewhere: `ChaCha20PrfBound`
  (in `Jasmin/ChaCha20Block.lean`) is an *assumption* that the ChaCha20 block
  function — built from `ChaCha20QR.quarterRound` via `quarterRoundAt`,
  `chachaBlock` — is a PRF. The leaf does **not** establish, and this file does
  **not** establish, that the emitted code is a PRF / IND-CPA / IND-CCA secure.

The tie proved here is *precisely*: the verified-compiler-emitted artifact
computes the **same function** `quarterRound` that the protocol's PRF assumption
quantifies over. Two independently-written reference definitions of the RFC 8439
§2.1 quarter-round agree:

* `ThirToComFront.chachaQRSpec` — the front's emit-side reference, written with
  `BitVec.rotateRight (32 - n)` (the front recognises `rotate_right` only);
* `ChaCha20QR.quarterRound` — the protocol/PRF-side reference, written with
  `rotL32 x n = (x <<< n) ||| (x >>> (32 - n))` (shift-or left-rotate).

Both are the same RFC 8439 quarter-round; the only difference is how left-rotate
is spelled. `chachaQR_eq_quarterRound` proves they are *equal* as functions, and
`qr{A,B,C,D}_emitted_eq_quarterRound` transports the leaf's denotation facts
across this equality, giving the headline:

> the verified compiler emits a program whose `BitVec 32` denotation is exactly
> the abstract `quarterRound` word that the ChaCha20 PRF assumption is stated
> over.

## Granularity

The tie is at the **quarter-round** granularity: that is where *both* a
verified-compiler emit-form (`qr*_compiles`) and a protocol-level abstract
function (`quarterRound`, the building block of `chachaBlock` / the PRF
assumption) exist. The full block (`chachaBlock`) is *not* emitted as a single
leaf, so no block-level functional tie is claimed.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxChachaTie

open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxChaCha
open CatCrypt.Crypto.Jasmin.ChaCha20QR (rotL32 quarterRound)
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)

/-! ## The two reference left-rotates agree -/

/-- The shift-or left-rotate used by the protocol-side reference equals the
    `rotateRight (32 - n)` form used by the front's emit-side reference, for the
    four ChaCha20 rotation counts `16, 12, 8, 7` (all `< 32`). -/
theorem rotL32_eq_rotateRight (x : BitVec 32) {n : Nat} (hn : n < 32) (hn0 : 0 < n) :
    rotL32 x n = x.rotateRight (32 - n) := by
  unfold rotL32
  interval_cases n <;> bv_decide

/-! ## The two RFC 8439 quarter-round references are the same function -/

/-- **Functional equality of the two quarter-round references.** The front's
    emit-side reference `chachaQRSpec` (used by the verified-compiler leaf) and
    the protocol/PRF-side reference `quarterRound` (the building block of the
    ChaCha20 block function the PRF assumption quantifies over) compute the same
    `(a', b', c', d')`. This is a pure functional fact: it says nothing about
    PRF security. -/
theorem chachaQR_eq_quarterRound (a b c d : BitVec 32) :
    chachaQRSpec a b c d = quarterRound a b c d := by
  simp only [chachaQRSpec, quarterRound,
    rotL32_eq_rotateRight (n := 16) _ (by omega) (by omega),
    rotL32_eq_rotateRight (n := 12) _ (by omega) (by omega),
    rotL32_eq_rotateRight (n := 8) _ (by omega) (by omega),
    rotL32_eq_rotateRight (n := 7) _ (by omega) (by omega)]

/-! ## Transport the leaf's denotation facts onto the protocol's abstract `quarterRound`

Each `qr*_emitted_eq_quarterRound` says: the verified compiler emits a program
`prog` whose `BitVec 32` denotation is exactly the corresponding word of the
abstract `quarterRound` that the ChaCha20 PRF assumption is stated over. This is
the functional-equality tie — NOT a statement that the emitted code is a PRF. -/

/-- The emitted `a'` leaf computes `(quarterRound a b c d).1` — the same first
    word the protocol's PRF assumption quantifies over. -/
theorem qrA_emitted_eq_quarterRound :
    ∃ (prog : Com jasminDialect (frontCtxt 32 4 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 4) ["a", "b", "c", "d"] qrASrc = some prog ∧
      ∀ (a b c d : BitVec 32),
        prog.denote (inputValuation 32 4 ![a, b, c, d])
          = (quarterRound a b c d).1 := by
  obtain ⟨prog, hc, hden⟩ := qrA_compiles
  refine ⟨prog, hc, fun a b c d => ?_⟩
  rw [hden a b c d, chachaQR_eq_quarterRound]

/-- The emitted `b'` leaf computes `(quarterRound a b c d).2.1`. -/
theorem qrB_emitted_eq_quarterRound :
    ∃ (prog : Com jasminDialect (frontCtxt 32 4 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 4) ["a", "b", "c", "d"] qrBSrc = some prog ∧
      ∀ (a b c d : BitVec 32),
        prog.denote (inputValuation 32 4 ![a, b, c, d])
          = (quarterRound a b c d).2.1 := by
  obtain ⟨prog, hc, hden⟩ := qrB_compiles
  refine ⟨prog, hc, fun a b c d => ?_⟩
  rw [hden a b c d, chachaQR_eq_quarterRound]

/-- The emitted `c'` leaf computes `(quarterRound a b c d).2.2.1`. -/
theorem qrC_emitted_eq_quarterRound :
    ∃ (prog : Com jasminDialect (frontCtxt 32 4 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 4) ["a", "b", "c", "d"] qrCSrc = some prog ∧
      ∀ (a b c d : BitVec 32),
        prog.denote (inputValuation 32 4 ![a, b, c, d])
          = (quarterRound a b c d).2.2.1 := by
  obtain ⟨prog, hc, hden⟩ := qrC_compiles
  refine ⟨prog, hc, fun a b c d => ?_⟩
  rw [hden a b c d, chachaQR_eq_quarterRound]

/-- The emitted `d'` leaf computes `(quarterRound a b c d).2.2.2`. -/
theorem qrD_emitted_eq_quarterRound :
    ∃ (prog : Com jasminDialect (frontCtxt 32 4 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 4) ["a", "b", "c", "d"] qrDSrc = some prog ∧
      ∀ (a b c d : BitVec 32),
        prog.denote (inputValuation 32 4 ![a, b, c, d])
          = (quarterRound a b c d).2.2.2 := by
  obtain ⟨prog, hc, hden⟩ := qrD_compiles
  refine ⟨prog, hc, fun a b c d => ?_⟩
  rw [hden a b c d, chachaQR_eq_quarterRound]

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxChachaTie
