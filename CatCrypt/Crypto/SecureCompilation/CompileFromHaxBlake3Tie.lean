/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHaxBlake3
import CatCrypt.Crypto.BLAKE3.CompressOwnedEmit

/-!
# #607 fan-out: functional tie — verified-compiler BLAKE3 G words = the reference `gSpec`

This module wires the committed **compile-from-hax BLAKE3 G leaves**
(`CompileFromHaxBlake3.blake3G{A,B,C,D}_compiles`) onto the BLAKE3 reference `g`
mixing function `BLAKE3.CompressOwnedEmit.gSpec` — the same state-update spec the
owned x86 BLAKE3 compress emit (`blake3_G_computes_spec`) and the whole-compress
bench (`bench/blake3_compare`) are written against.

## What this is — and what it is NOT (honest framing)

This is a **functional-equality** tie, not a security claim.

- Each compile-from-hax leaf proves a *functional-correctness* fact: the artifact
  emitted by the verified compiler computes a closed-form BLAKE3 reference `g`
  output word (`blake3GSpec`, a 4-tuple stated locally in the leaf module).
- This file transports each such denotation onto the **named reference**
  `CompressOwnedEmit.gSpec`, the state-update form used by the rest of the BLAKE3
  emit/bench layer, applied to the canonical input state (slots `0,1,2,3 = a,b,c,d`)
  and read back at the corresponding output slot.
- BLAKE3 compress is an unkeyed primitive; there is no CR/PRF claim here, only
  `<emit-form> = <reference g word>`.

## §1  The leaf's `blake3GSpec` words equal the reference `gSpec` output slots

`gSpec` is the state-update form: `gSpec s 0 1 2 3 m0 m1` returns a 16-word state
whose slots `0,1,2,3` hold the updated `a',b',c',d'`. Feeding the canonical input
state `inSt a b c d` (slot `i` = `[a,b,c,d]ᵢ` for `i < 4`, `0` elsewhere), each
updated slot equals the corresponding component of the leaf's `blake3GSpec`. Both
sides use `BitVec.rotateRight` with counts `16,12,8,7`, so each `*_eq_g` is a
slot-projection of the same SSA.

## §2  Transport the leaf denotations onto the reference `gSpec`

Each `blake3G{A,B,C,D}_emitted_eq_g` says: the verified compiler emits a program
whose `BitVec 32` denotation is exactly the corresponding updated slot of
`gSpec (inSt a b c d) 0 1 2 3 m0 m1`. Functional-equality tie — NOT a security claim.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxBlake3Tie

open CatCrypt.Crypto.SecureCompilation.ThirToComFront (inputValuation frontCtxt rW)
open CatCrypt.Crypto.SecureCompilation.CompileFromHax (compileFromHax)
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxBlake3
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)
open CatCrypt.Crypto.BLAKE3.CompressOwnedEmit (St gSpec)

/-- The canonical BLAKE3 input state: slots `0,1,2,3` carry the four state words
    `a,b,c,d`, the remaining slots carry `0` (irrelevant — `gSpec` on slots
    `0,1,2,3` reads only those four). -/
def inSt (a b c d : BitVec 32) : St
  | 0 => a | 1 => b | 2 => c | 3 => d | _ => 0

/-! ## §1  The leaf's `blake3GSpec` words equal the reference `gSpec` output slots -/

/-- The leaf's `a'` word equals the reference `g`'s updated slot `0`. -/
theorem blake3GaSpec_eq_g (a b c d m0 m1 : BitVec 32) :
    (blake3GSpec a b c d m0 m1).1 = gSpec (inSt a b c d) 0 1 2 3 m0 m1 0 := by
  simp [blake3GSpec, gSpec, CatCrypt.Crypto.BLAKE3.CompressOwnedEmit.St.set,
    CatCrypt.Crypto.BLAKE3.CompressOwnedEmit.rotr, inSt]

/-- The leaf's `b'` word equals the reference `g`'s updated slot `1`. -/
theorem blake3GbSpec_eq_g (a b c d m0 m1 : BitVec 32) :
    (blake3GSpec a b c d m0 m1).2.1 = gSpec (inSt a b c d) 0 1 2 3 m0 m1 1 := by
  simp [blake3GSpec, gSpec, CatCrypt.Crypto.BLAKE3.CompressOwnedEmit.St.set,
    CatCrypt.Crypto.BLAKE3.CompressOwnedEmit.rotr, inSt]

/-- The leaf's `c'` word equals the reference `g`'s updated slot `2`. -/
theorem blake3GcSpec_eq_g (a b c d m0 m1 : BitVec 32) :
    (blake3GSpec a b c d m0 m1).2.2.1 = gSpec (inSt a b c d) 0 1 2 3 m0 m1 2 := by
  simp [blake3GSpec, gSpec, CatCrypt.Crypto.BLAKE3.CompressOwnedEmit.St.set,
    CatCrypt.Crypto.BLAKE3.CompressOwnedEmit.rotr, inSt]

/-- The leaf's `d'` word equals the reference `g`'s updated slot `3`. -/
theorem blake3GdSpec_eq_g (a b c d m0 m1 : BitVec 32) :
    (blake3GSpec a b c d m0 m1).2.2.2 = gSpec (inSt a b c d) 0 1 2 3 m0 m1 3 := by
  simp [blake3GSpec, gSpec, CatCrypt.Crypto.BLAKE3.CompressOwnedEmit.St.set,
    CatCrypt.Crypto.BLAKE3.CompressOwnedEmit.rotr, inSt]

/-! ## §2  Transport the leaf denotations onto the reference `gSpec` -/

/-- The emitted BLAKE3 G `a'` leaf computes `gSpec (inSt a b c d) 0 1 2 3 m0 m1 0`. -/
theorem blake3GA_emitted_eq_g :
    ∃ (prog : Com jasminDialect (frontCtxt 32 6 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 6) ["a", "b", "c", "d", "m0", "m1"] gASrc = some prog ∧
      ∀ (a b c d m0 m1 : BitVec 32),
        prog.denote (inputValuation 32 6 ![a, b, c, d, m0, m1])
          = gSpec (inSt a b c d) 0 1 2 3 m0 m1 0 := by
  obtain ⟨prog, hc, hden⟩ := blake3GA_compiles
  exact ⟨prog, hc, fun a b c d m0 m1 => (hden a b c d m0 m1).trans (blake3GaSpec_eq_g a b c d m0 m1)⟩

/-- The emitted BLAKE3 G `b'` leaf computes `gSpec (inSt a b c d) 0 1 2 3 m0 m1 1`. -/
theorem blake3GB_emitted_eq_g :
    ∃ (prog : Com jasminDialect (frontCtxt 32 6 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 6) ["a", "b", "c", "d", "m0", "m1"] gBSrc = some prog ∧
      ∀ (a b c d m0 m1 : BitVec 32),
        prog.denote (inputValuation 32 6 ![a, b, c, d, m0, m1])
          = gSpec (inSt a b c d) 0 1 2 3 m0 m1 1 := by
  obtain ⟨prog, hc, hden⟩ := blake3GB_compiles
  exact ⟨prog, hc, fun a b c d m0 m1 => (hden a b c d m0 m1).trans (blake3GbSpec_eq_g a b c d m0 m1)⟩

/-- The emitted BLAKE3 G `c'` leaf computes `gSpec (inSt a b c d) 0 1 2 3 m0 m1 2`. -/
theorem blake3GC_emitted_eq_g :
    ∃ (prog : Com jasminDialect (frontCtxt 32 6 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 6) ["a", "b", "c", "d", "m0", "m1"] gCSrc = some prog ∧
      ∀ (a b c d m0 m1 : BitVec 32),
        prog.denote (inputValuation 32 6 ![a, b, c, d, m0, m1])
          = gSpec (inSt a b c d) 0 1 2 3 m0 m1 2 := by
  obtain ⟨prog, hc, hden⟩ := blake3GC_compiles
  exact ⟨prog, hc, fun a b c d m0 m1 => (hden a b c d m0 m1).trans (blake3GcSpec_eq_g a b c d m0 m1)⟩

/-- The emitted BLAKE3 G `d'` leaf computes `gSpec (inSt a b c d) 0 1 2 3 m0 m1 3`. -/
theorem blake3GD_emitted_eq_g :
    ∃ (prog : Com jasminDialect (frontCtxt 32 6 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 6) ["a", "b", "c", "d", "m0", "m1"] gDSrc = some prog ∧
      ∀ (a b c d m0 m1 : BitVec 32),
        prog.denote (inputValuation 32 6 ![a, b, c, d, m0, m1])
          = gSpec (inSt a b c d) 0 1 2 3 m0 m1 3 := by
  obtain ⟨prog, hc, hden⟩ := blake3GD_compiles
  exact ⟨prog, hc, fun a b c d m0 m1 => (hden a b c d m0 m1).trans (blake3GdSpec_eq_g a b c d m0 m1)⟩

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxBlake3Tie
