/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.ReifyBitwise
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.HaxBitwise
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.HaxLoops

/-!
# `reifyAeneas%` on the output of the hax Lean backend

Five functions of the output of the hax 0.4.2 Lean backend on the Aeneas test crates
(`HaxBitwise`, `HaxLoops`, copied unchanged) read as NF programs by `reifyAeneas%`, each with the
statement that a value of the function is, embedded, the denotation of its program in the
compiler's semantics `PDenP hax64WExit` from some fuel on (`Reify.toDenote`).

* pure bitwise operations printed as values: `bitwise.xor_u32` (`ok (a ^^^ b)`),
  `bitwise.or_u32` (`ok (a ||| b)`), `bitwise.and_u32` (`ok (a &&& b)`), read by
  `reifyE_bxor_ok`, `reifyE_bor_ok`, `reifyE_band_ok`;
* shifts by a `usize` literal: `bitwise.shift_u32` (`a >>> 16#usize`, then `<<< 16#usize`),
  read by `reifyE_shr` and `reifyE_shl` with the literal bound first;
* a loop from a literal: `loops.iter` (`iter_loop max 0#u32`), read by `Reify.loopLit`.

## Main results

* `xorU32_denote`, `orU32_denote`, `andU32_denote`, `shiftU32_denote`, `iter_denote`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.Hax

open Aeneas.Std
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.AeneasFront
open CatCrypt.Crypto.Hax (hax64WExit)
open CatCrypt.Crypto.Hax.ImpToNF (PDenP)

/-- `bitwise.xor_u32` read as an NF program. -/
def xorU32 := reifyAeneas% bitwise.xor_u32

/-- A value of `bitwise.xor_u32` is the denotation of its NF program. -/
theorem xorU32_denote (a b z : U32) (h : bitwise.xor_u32 a b = .ok z) :
    ∃ N, ∀ fuel, N ≤ fuel → PDenP hax64WExit fuel xorU32.prog (vCons a (vCons b vNil)) =
      some (.cons (embW z) .nil) :=
  Reify.toDenote (xorU32.sound a b) h

/-- `bitwise.or_u32` read as an NF program. -/
def orU32 := reifyAeneas% bitwise.or_u32

/-- A value of `bitwise.or_u32` is the denotation of its NF program. -/
theorem orU32_denote (a b z : U32) (h : bitwise.or_u32 a b = .ok z) :
    ∃ N, ∀ fuel, N ≤ fuel → PDenP hax64WExit fuel orU32.prog (vCons a (vCons b vNil)) =
      some (.cons (embW z) .nil) :=
  Reify.toDenote (orU32.sound a b) h

/-- `bitwise.and_u32` read as an NF program. -/
def andU32 := reifyAeneas% bitwise.and_u32

/-- A value of `bitwise.and_u32` is the denotation of its NF program. -/
theorem andU32_denote (a b z : U32) (h : bitwise.and_u32 a b = .ok z) :
    ∃ N, ∀ fuel, N ≤ fuel → PDenP hax64WExit fuel andU32.prog (vCons a (vCons b vNil)) =
      some (.cons (embW z) .nil) :=
  Reify.toDenote (andU32.sound a b) h

/-- `bitwise.shift_u32` read as an NF program. -/
def shiftU32 := reifyAeneas% bitwise.shift_u32

/-- A value of `bitwise.shift_u32` is the denotation of its NF program. -/
theorem shiftU32_denote (a z : U32) (h : bitwise.shift_u32 a = .ok z) :
    ∃ N, ∀ fuel, N ≤ fuel → PDenP hax64WExit fuel shiftU32.prog (vCons a vNil) =
      some (.cons (embW z) .nil) :=
  Reify.toDenote (shiftU32.sound a) h

/-- `loops.iter` read as an NF program. -/
def iterP := reifyAeneas% loops.iter

/-- A value of `loops.iter` is the denotation of its NF program. -/
theorem iter_denote (max z : U32) (h : loops.iter max = .ok z) :
    ∃ N, ∀ fuel, N ≤ fuel → PDenP hax64WExit fuel iterP.prog (vCons max vNil) =
      some (.cons (embW z) .nil) :=
  Reify.toDenote (iterP.sound max) h

end CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.Hax
