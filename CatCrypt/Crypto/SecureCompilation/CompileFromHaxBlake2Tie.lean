/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxBlake2
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Blake2Emit

/-!
# #607 fan-out: functional tie — verified-compiler BLAKE2s G output word = the reference `gSpec`

This module wires the committed **compile-from-hax BLAKE2s G leaf**
(`CompileFromHaxBlake2.blake2G_compiles`, the final `a'` word) onto the BLAKE2
reference `G` mixing function `X86Backend.Blake2Emit.gSpec` — the same
state-update spec the owned x86 BLAKE2 emit (`blake2s_G_computes_spec`) and the
BLAKE2 bench are written against (RFC 7693 §3.1, BLAKE2s rotates `16,12,8,7`).

## What this is — and what it is NOT

This is a **functional-equality** tie, not a security claim.

- The compile-from-hax leaf proves a *functional-correctness* fact: the artifact
  emitted by the verified compiler computes the closed-form BLAKE2s G output word
  `blake2GSpec` (the final `a` word, stated locally in the leaf module).
- This file transports that denotation onto the **named reference**
  `Blake2Emit.gSpec`, applied to the canonical input state
  (slots `0,1,2,3 = a,b,c,d`) at the BLAKE2s rotates `16,12,8,7`, read back at the
  output slot `0` (the updated `a'`). Since the BLAKE2 G mixing leaves the `a`
  word untouched after the second message injection, that slot is exactly the
  leaf's `blake2GSpec`.
- BLAKE2s is an unkeyed compression primitive; there is no CR/PRF claim here,
  only `<emit-form> = <reference g word>`.

## Granularity note

The leaf emits only the **final `a` word** (the front returns a single register;
see `CompileFromHaxBlake2`'s module doc). The full four-word G is the same
`+`/`^`/`>>>` shape replicated; this tie is at the `a'`-word granularity, the only
output the leaf emits.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxBlake2Tie

open CatCrypt.Crypto.SecureCompilation.ThirToComFront (inputValuation frontCtxt rW)
open CatCrypt.Crypto.SecureCompilation.CompileFromHax (compileFromHax)
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxBlake2
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Blake2Emit (St gSpec)

/-- The canonical BLAKE2s input work vector: slots `0,1,2,3` carry the four state
    words `a,b,c,d`, the remaining slots carry `0` (irrelevant — `gSpec` on slots
    `0,1,2,3` reads only those four). -/
def inSt (a b c d : BitVec 32) : St 32
  | 0 => a | 1 => b | 2 => c | 3 => d | _ => 0

/-! ## §1  The leaf's `blake2GSpec` word equals the reference `gSpec` updated slot `0` -/

/-- The leaf's final `a'` word equals the BLAKE2 reference `g`'s updated slot `0`
    (BLAKE2s rotates `16,12,8,7`). `gSpec` does not change the `a` slot after the
    second message injection, so its slot `0` is exactly the leaf's `blake2GSpec`. -/
theorem blake2GSpec_eq_g (a b c d x y : BitVec 32) :
    blake2GSpec a b c d x y = gSpec (inSt a b c d) 0 1 2 3 x y 16 12 8 7 0 := by
  simp [blake2GSpec, gSpec, CatCrypt.Crypto.SecureCompilation.X86Backend.Blake2Emit.St.set,
    CatCrypt.Crypto.SecureCompilation.X86Backend.Blake2Emit.rotr, inSt]

/-! ## §2  Transport the leaf denotation onto the reference `gSpec` -/

/-- The emitted BLAKE2s G `a'` leaf computes `gSpec (inSt a b c d) 0 1 2 3 x y 16 12 8 7 0` —
    the BLAKE2 reference `g` updated `a` word. Functional-equality tie — NOT a
    security claim. -/
theorem blake2G_emitted_eq_g :
    ∃ (prog : Com jasminDialect (frontCtxt 32 6 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 6) ["a", "b", "c", "d", "x", "y"] blake2GSrc = some prog ∧
      ∀ (a b c d x y : BitVec 32),
        prog.denote (inputValuation 32 6 ![a, b, c, d, x, y])
          = gSpec (inSt a b c d) 0 1 2 3 x y 16 12 8 7 0 := by
  obtain ⟨prog, hc, hden⟩ := blake2G_compiles
  exact ⟨prog, hc, fun a b c d x y => (hden a b c d x y).trans (blake2GSpec_eq_g a b c d x y)⟩

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxBlake2Tie
