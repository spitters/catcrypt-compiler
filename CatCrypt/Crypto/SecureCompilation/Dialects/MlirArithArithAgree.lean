/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.Arith
public import CatCrypt.Crypto.SecureCompilation.VIR.MlirArithDialect

/-!
# Integer-fragment semantic agreement: FRONT `mlirArithDialect` ≡ BACK `arithDialect`

The MLIR dialect-alignment restructure has **two** denoting `arith` dialects:

* the **front** `mlirArithDialect`
  (`VIR/MlirArithDialect.lean`, over `CryptoTy`, where `⟦.sword w⟧ = BitVec w`),
  the semantic foundation under the `CatCryptOp.toArithOpCode` emission pass; and
* the **back** `arithDialect`
  (`Dialects/Arith.lean`, over `ArithTy`, where `⟦.int w⟧ = BitVec w`),
  the target-neutral D0 lowering baseline that maps 1:1 into `jasminDialect`.

These are **not** the same Lean object: their value-type universes differ
(`CryptoTy` vs `ArithTy`), so their raw `DialectDenote.denote` functions live
over *different* `HVector` argument domains and are **not** directly `rfl`-equal
(and comparing them as functions would require `HEq`). This file proves they are
nonetheless **one arith at two layers** — they realise *identical* `BitVec`
semantics on the shared integer fragment — using the **extensional** formulation
that avoids `HEq` entirely.

## The shared integer fragment

For each shared op we build the argument `HVector` explicitly from `BitVec w`
values (`.cons`/`.nil`) and show each dialect's denotation computes the intended
`BitVec` operation. The two `_apply` lemmas have argument `HVector`s of
*different types* (over `CryptoTy` vs `ArithTy`) but their **results** are the
same `BitVec w`, so the `_agree` equation is well-typed and closes by rewriting
both sides to the common `BitVec` operation.

| op           | shared `BitVec` meaning  | back (`arithDialect`)  | front (`mlirArithDialect`) |
|--------------|--------------------------|------------------------|----------------------------|
| `addi w`     | `· + ·`                  | `addi w`               | `addi w`                   |
| `subi w`     | `· - ·`                  | `subi w`               | `subi w`                   |
| `muli w`     | `· * ·`                  | `muli w`               | `muli w`                   |
| `andi w`     | `· &&& ·`                | `andi w`               | `andi w`                   |
| `ori  w`     | `· ||| ·`                | `ori w`                | `ori w`                    |
| `xori w`     | `· ^^^ ·`                | `xori w`               | `xori w`                   |
| `· <<< shiftMask w n` | `BitVec.shiftLeft` | `shli_imm w n`        | `shli w n`                 |
| `· >>> shiftMask w n` | `BitVec.ushiftRight` | `shrui_imm w n`     | `shrui w n`                |
| `constant`   | the literal `BitVec`     | `constant w v.toNat`   | `constant w v`             |

The two right-shift denotations (`a >>> n` back vs `BitVec.ushiftRight a n`
front) are **definitionally equal** (`>>>` on `BitVec` *is* `BitVec.ushiftRight`),
so `shrui` agrees by the same `rfl`/rewrite as the rest — no bridge lemma needed.

The constant ops carry different payloads: the back op carries a `Nat`
(`constant w n ↦ BitVec.ofNat w n`), the front a `BitVec w` value
(`constant w v ↦ v`). They agree under the alignment `n := v.toNat`, using
`BitVec.ofNat w v.toNat = v` (via `BitVec.ofNat_toNat` + `BitVec.setWidth_eq`).

## Out of the shared fragment

* `mului_extended_hi w` is **back-only** (the widening-multiply high half, whose
  jasmin image is `mulhi`); the front has no such op.
* `cmpi`/`select`/`extsi` and the `i1`/`bit`-typed ops
  (`xori1`/`andi1`/`ori1`/`cmpi1`/`xnori1`/`constantBit`) are **front-only**:
  they target `arith` opcodes the D0 back-end baseline does not carry.

The `agree_*` lemmas below cover exactly the 9 ops in the shared fragment.
-/

@[expose] public section

set_option autoImplicit false

-- (front ≡ back arith, integer fragment)
namespace CatCrypt.Crypto.SecureCompilation.Dialects.MlirArithArithAgree

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.Dialects.Arith
open CatCrypt.Crypto.SecureCompilation.VIR.MlirArithDialect

/-! ## 1. Binary ALU ops (`addi`/`subi`/`muli`/`andi`/`ori`/`xori`)

Each op, applied to an explicitly built two-element `BitVec w` argument vector,
denotes to the intended `BitVec` operation in **both** dialects; hence they agree. -/

/-! ### `addi` -/

theorem arith_addi_apply (w : Nat) (a b : BitVec w) :
    DialectDenote.denote (d := arithDialect) (.addi w) (.cons a (.cons b .nil)) = a + b := rfl

theorem mlirArith_addi_apply (w : Nat) (a b : BitVec w) :
    DialectDenote.denote (d := mlirArithDialect) (.addi w) (.cons a (.cons b .nil)) = a + b := rfl

/-- The front `addi` and back `addi` compute the same `BitVec` sum. -/
theorem addi_agree (w : Nat) (a b : BitVec w) :
    DialectDenote.denote (d := arithDialect) (.addi w) (.cons a (.cons b .nil))
      = DialectDenote.denote (d := mlirArithDialect) (.addi w) (.cons a (.cons b .nil)) := by
  rw [arith_addi_apply, mlirArith_addi_apply]

/-! ### `subi` -/

theorem arith_subi_apply (w : Nat) (a b : BitVec w) :
    DialectDenote.denote (d := arithDialect) (.subi w) (.cons a (.cons b .nil)) = a - b := rfl

theorem mlirArith_subi_apply (w : Nat) (a b : BitVec w) :
    DialectDenote.denote (d := mlirArithDialect) (.subi w) (.cons a (.cons b .nil)) = a - b := rfl

/-- The front `subi` and back `subi` compute the same `BitVec` difference. -/
theorem subi_agree (w : Nat) (a b : BitVec w) :
    DialectDenote.denote (d := arithDialect) (.subi w) (.cons a (.cons b .nil))
      = DialectDenote.denote (d := mlirArithDialect) (.subi w) (.cons a (.cons b .nil)) := by
  rw [arith_subi_apply, mlirArith_subi_apply]

/-! ### `muli` -/

theorem arith_muli_apply (w : Nat) (a b : BitVec w) :
    DialectDenote.denote (d := arithDialect) (.muli w) (.cons a (.cons b .nil)) = a * b := rfl

theorem mlirArith_muli_apply (w : Nat) (a b : BitVec w) :
    DialectDenote.denote (d := mlirArithDialect) (.muli w) (.cons a (.cons b .nil)) = a * b := rfl

/-- The front `muli` and back `muli` compute the same `BitVec` product. -/
theorem muli_agree (w : Nat) (a b : BitVec w) :
    DialectDenote.denote (d := arithDialect) (.muli w) (.cons a (.cons b .nil))
      = DialectDenote.denote (d := mlirArithDialect) (.muli w) (.cons a (.cons b .nil)) := by
  rw [arith_muli_apply, mlirArith_muli_apply]

/-! ### `andi` -/

theorem arith_andi_apply (w : Nat) (a b : BitVec w) :
    DialectDenote.denote (d := arithDialect) (.andi w) (.cons a (.cons b .nil)) = a &&& b := rfl

theorem mlirArith_andi_apply (w : Nat) (a b : BitVec w) :
    DialectDenote.denote (d := mlirArithDialect) (.andi w) (.cons a (.cons b .nil)) = a &&& b := rfl

/-- The front `andi` and back `andi` compute the same `BitVec` bitwise-and. -/
theorem andi_agree (w : Nat) (a b : BitVec w) :
    DialectDenote.denote (d := arithDialect) (.andi w) (.cons a (.cons b .nil))
      = DialectDenote.denote (d := mlirArithDialect) (.andi w) (.cons a (.cons b .nil)) := by
  rw [arith_andi_apply, mlirArith_andi_apply]

/-! ### `ori` -/

theorem arith_ori_apply (w : Nat) (a b : BitVec w) :
    DialectDenote.denote (d := arithDialect) (.ori w) (.cons a (.cons b .nil)) = a ||| b := rfl

theorem mlirArith_ori_apply (w : Nat) (a b : BitVec w) :
    DialectDenote.denote (d := mlirArithDialect) (.ori w) (.cons a (.cons b .nil)) = a ||| b := rfl

/-- The front `ori` and back `ori` compute the same `BitVec` bitwise-or. -/
theorem ori_agree (w : Nat) (a b : BitVec w) :
    DialectDenote.denote (d := arithDialect) (.ori w) (.cons a (.cons b .nil))
      = DialectDenote.denote (d := mlirArithDialect) (.ori w) (.cons a (.cons b .nil)) := by
  rw [arith_ori_apply, mlirArith_ori_apply]

/-! ### `xori` -/

theorem arith_xori_apply (w : Nat) (a b : BitVec w) :
    DialectDenote.denote (d := arithDialect) (.xori w) (.cons a (.cons b .nil)) = a ^^^ b := rfl

theorem mlirArith_xori_apply (w : Nat) (a b : BitVec w) :
    DialectDenote.denote (d := mlirArithDialect) (.xori w) (.cons a (.cons b .nil)) = a ^^^ b := rfl

/-- The front `xori` and back `xori` compute the same `BitVec` bitwise-xor. -/
theorem xori_agree (w : Nat) (a b : BitVec w) :
    DialectDenote.denote (d := arithDialect) (.xori w) (.cons a (.cons b .nil))
      = DialectDenote.denote (d := mlirArithDialect) (.xori w) (.cons a (.cons b .nil)) := by
  rw [arith_xori_apply, mlirArith_xori_apply]

/-! ## 2. Immediate shifts (`shli`/`shrui`)

Unary ops (one `BitVec w` argument). Note the name difference: the back op is
`shli_imm w n`/`shrui_imm w n`, the front is `shli w n`/`shrui w n`. -/

/-! ### `shli` / `shli_imm` -/

theorem arith_shli_apply (w n : Nat) (a : BitVec w) :
    DialectDenote.denote (d := arithDialect) (.shli_imm w n) (.cons a .nil)
      = a <<< shiftMask w n := rfl

theorem mlirArith_shli_apply (w n : Nat) (a : BitVec w) :
    DialectDenote.denote (d := mlirArithDialect) (.shli w n) (.cons a .nil)
      = a <<< shiftMask w n := rfl

/-- The front `shli` and back `shli_imm` compute the same `BitVec` left shift. -/
theorem shli_agree (w n : Nat) (a : BitVec w) :
    DialectDenote.denote (d := arithDialect) (.shli_imm w n) (.cons a .nil)
      = DialectDenote.denote (d := mlirArithDialect) (.shli w n) (.cons a .nil) := by
  rw [arith_shli_apply, mlirArith_shli_apply]

/-! ### `shrui` / `shrui_imm`

The back op denotes via `a >>> n`, the front via `BitVec.ushiftRight a n`. On
`BitVec`, `· >>> ·` **is** `BitVec.ushiftRight`, so the two are definitionally
equal and both `_apply` lemmas close by `rfl` against the same RHS — **no bridge
lemma is required**. -/

theorem arith_shrui_apply (w n : Nat) (a : BitVec w) :
    DialectDenote.denote (d := arithDialect) (.shrui_imm w n) (.cons a .nil)
      = BitVec.ushiftRight a (shiftMask w n) := rfl

theorem mlirArith_shrui_apply (w n : Nat) (a : BitVec w) :
    DialectDenote.denote (d := mlirArithDialect) (.shrui w n) (.cons a .nil)
      = BitVec.ushiftRight a (shiftMask w n) := rfl

/-- The front `shrui` and back `shrui_imm` compute the same `BitVec` logical
    right shift (the back `· >>> ·` is definitionally `BitVec.ushiftRight`). -/
theorem shrui_agree (w n : Nat) (a : BitVec w) :
    DialectDenote.denote (d := arithDialect) (.shrui_imm w n) (.cons a .nil)
      = DialectDenote.denote (d := mlirArithDialect) (.shrui w n) (.cons a .nil) := by
  rw [arith_shrui_apply, mlirArith_shrui_apply]

/-! ## 3. Constant materialisation (`constant`)

The back op carries a `Nat` (`constant w n ↦ BitVec.ofNat w n`); the front
carries a `BitVec w` value (`constant w v ↦ v`). They agree under the alignment
`n := v.toNat`, since `BitVec.ofNat w v.toNat = v`. -/

theorem arith_constant_apply (w n : Nat) :
    DialectDenote.denote (d := arithDialect) (.constant w n) .nil = BitVec.ofNat w n := rfl

theorem mlirArith_constant_apply (w : Nat) (v : BitVec w) :
    DialectDenote.denote (d := mlirArithDialect) (.constant w v) .nil = v := rfl

/-- `BitVec.ofNat w v.toNat = v`: materialising a value's `Nat` interpretation at
    its own width is the identity. The constant-alignment bridge. -/
theorem ofNat_toNat_self (w : Nat) (v : BitVec w) : BitVec.ofNat w v.toNat = v := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The back `constant w v.toNat` and front `constant w v` materialise the same
    `BitVec` literal. -/
theorem constant_agree (w : Nat) (v : BitVec w) :
    DialectDenote.denote (d := arithDialect) (.constant w v.toNat) .nil
      = DialectDenote.denote (d := mlirArithDialect) (.constant w v) .nil := by
  rw [arith_constant_apply, mlirArith_constant_apply, ofNat_toNat_self]

/-! ## 4. Summary

The nine `*_agree` lemmas above certify that the FRONT `mlirArithDialect` and
the BACK `arithDialect` assign **identical** `BitVec` semantics to every op of
the shared integer fragment (binary ALU `addi`/`subi`/`muli`/`andi`/`ori`/`xori`,
the immediate shifts `shli`/`shrui`, and the materialised `constant`). They are
**one arith realised at two layers** — the documented connecting step between the
front emission semantics and the back D0 lowering baseline — not two divergent
duplicate dialects.

Out of the shared fragment: `mului_extended_hi` is back-only, and
`cmpi`/`select`/`extsi`/`xori1`/`andi1`/`ori1`/`cmpi1`/`xnori1`/`constantBit` are
front-only. -/

end CatCrypt.Crypto.SecureCompilation.Dialects.MlirArithArithAgree
