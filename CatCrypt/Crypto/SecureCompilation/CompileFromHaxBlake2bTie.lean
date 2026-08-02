/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHaxBlake2b

/-!
# #607 fan-out: functional tie — verified-compiler BLAKE2b G words = the front's `blake2bGSpec`

This module wires the committed **compile-from-hax BLAKE2b G leaves**
(`CompileFromHaxBlake2b.blake2bG{A,B,C,D}_compiles`) onto the front's RFC 7693
reference `ThirToComFront.blake2bGSpec` — the same 4-tuple BLAKE2b G output word
spec that the `thirDialect` self-consistency checks (`ThirToComFront.gA_via_thirDialect`
…) and the owned x86 emit (`X86Backend.Blake2bGThirEmit`) are written against.

## What this is — and what it is NOT

This is a **functional-equality** tie, not a security claim.

- Each compile-from-hax leaf proves a *functional-correctness* fact: the artifact
  emitted by the verified compiler computes a closed-form RFC 7693 BLAKE2b G
  output word (`blake2bG{a,b,c,d}Spec`, stated locally in the leaf module).
- This file transports each such denotation onto the **named front reference**
  `ThirToComFront.blake2bGSpec`'s corresponding component, so that "what the
  verified compiler emits" is literally "the front's RFC 7693 G word".
- BLAKE2b is an unkeyed compression primitive; there is no CR/PRF claim here,
  only `<emit-form> = <front spec word>`.

## §1  The leaf's per-word specs equal the front's `blake2bGSpec` components

The leaf module `CompileFromHaxBlake2b` states each output word as a standalone
`def` (`blake2bGaSpec` … `blake2bGdSpec`). They are the *same* SSA as
`ThirToComFront.blake2bGSpec` (RFC 7693 §3.1, rotates `32/24/16/63`), differing
only in spelling (local `let` chain vs. the front's tuple). Each `*_eq_front`
proves the two agree by definitional reduction.

## §2  Transport the leaf denotations onto the front spec

Each `blake2bG{A,B,C,D}_emitted_eq_front` says: the verified compiler emits a
program whose `BitVec 64` denotation is exactly the corresponding component of
`ThirToComFront.blake2bGSpec`. Functional-equality tie — NOT a security claim.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxBlake2bTie

open CatCrypt.Crypto.SecureCompilation.ThirToComFront (inputValuation frontCtxt rW blake2bGSpec)
open CatCrypt.Crypto.SecureCompilation.CompileFromHax (compileFromHax)
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxBlake2b
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)

/-! ## §1  The leaf's per-word specs equal the front's `blake2bGSpec` components -/

/-- The leaf's `a'` word spec equals `(blake2bGSpec a b c d x y).1`. -/
theorem blake2bGaSpec_eq_front (a b c d x y : BitVec 64) :
    blake2bGaSpec a b c d x y = (blake2bGSpec a b c d x y).1 := rfl

/-- The leaf's `b'` word spec equals `(blake2bGSpec a b c d x y).2.1`. -/
theorem blake2bGbSpec_eq_front (a b c d x y : BitVec 64) :
    blake2bGbSpec a b c d x y = (blake2bGSpec a b c d x y).2.1 := rfl

/-- The leaf's `c'` word spec equals `(blake2bGSpec a b c d x y).2.2.1`. -/
theorem blake2bGcSpec_eq_front (a b c d x y : BitVec 64) :
    blake2bGcSpec a b c d x y = (blake2bGSpec a b c d x y).2.2.1 := rfl

/-- The leaf's `d'` word spec equals `(blake2bGSpec a b c d x y).2.2.2`. -/
theorem blake2bGdSpec_eq_front (a b c d x y : BitVec 64) :
    blake2bGdSpec a b c d x y = (blake2bGSpec a b c d x y).2.2.2 := rfl

/-! ## §2  Transport the leaf denotations onto the front spec -/

/-- The emitted BLAKE2b G `a'` leaf computes `(blake2bGSpec a b c d x y).1`. -/
theorem blake2bGA_emitted_eq_front :
    ∃ (prog : Com jasminDialect (frontCtxt 64 6 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 6) ["a", "b", "c", "d", "x", "y"] blake2bGASrc = some prog ∧
      ∀ (a b c d x y : BitVec 64),
        prog.denote (inputValuation 64 6 ![a, b, c, d, x, y])
          = (blake2bGSpec a b c d x y).1 := by
  obtain ⟨prog, hc, hden⟩ := blake2bGA_compiles
  exact ⟨prog, hc, fun a b c d x y => (hden a b c d x y).trans (blake2bGaSpec_eq_front a b c d x y)⟩

/-- The emitted BLAKE2b G `b'` leaf computes `(blake2bGSpec a b c d x y).2.1`. -/
theorem blake2bGB_emitted_eq_front :
    ∃ (prog : Com jasminDialect (frontCtxt 64 6 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 6) ["a", "b", "c", "d", "x", "y"] blake2bGBSrc = some prog ∧
      ∀ (a b c d x y : BitVec 64),
        prog.denote (inputValuation 64 6 ![a, b, c, d, x, y])
          = (blake2bGSpec a b c d x y).2.1 := by
  obtain ⟨prog, hc, hden⟩ := blake2bGB_compiles
  exact ⟨prog, hc, fun a b c d x y => (hden a b c d x y).trans (blake2bGbSpec_eq_front a b c d x y)⟩

/-- The emitted BLAKE2b G `c'` leaf computes `(blake2bGSpec a b c d x y).2.2.1`. -/
theorem blake2bGC_emitted_eq_front :
    ∃ (prog : Com jasminDialect (frontCtxt 64 6 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 6) ["a", "b", "c", "d", "x", "y"] blake2bGCSrc = some prog ∧
      ∀ (a b c d x y : BitVec 64),
        prog.denote (inputValuation 64 6 ![a, b, c, d, x, y])
          = (blake2bGSpec a b c d x y).2.2.1 := by
  obtain ⟨prog, hc, hden⟩ := blake2bGC_compiles
  exact ⟨prog, hc, fun a b c d x y => (hden a b c d x y).trans (blake2bGcSpec_eq_front a b c d x y)⟩

/-- The emitted BLAKE2b G `d'` leaf computes `(blake2bGSpec a b c d x y).2.2.2`. -/
theorem blake2bGD_emitted_eq_front :
    ∃ (prog : Com jasminDialect (frontCtxt 64 6 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 6) ["a", "b", "c", "d", "x", "y"] blake2bGDSrc = some prog ∧
      ∀ (a b c d x y : BitVec 64),
        prog.denote (inputValuation 64 6 ![a, b, c, d, x, y])
          = (blake2bGSpec a b c d x y).2.2.2 := by
  obtain ⟨prog, hc, hden⟩ := blake2bGD_compiles
  exact ⟨prog, hc, fun a b c d x y => (hden a b c d x y).trans (blake2bGdSpec_eq_front a b c d x y)⟩

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxBlake2bTie
