/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxSha512
public import CatCrypt.Crypto.Util.Sha512Verified

/-!
# DIRECT functional ties — SHA-512 compile-from-hax leaves = FIPS spec fns

This module is the **width-64** companion to `CompileFromHaxSha2KeccakTie` (which ties the
SHA-256 / width-32 round components). It wires the committed **compile-from-hax SHA-512
round/schedule-component leaves**
(`CompileFromHaxSha512.{maj512,ch512,bigSigma0_512,bigSigma1_512,sigma0_512,sigma1_512}_compiles`)
onto the **abstract FIPS reference functions** the rest of CatCrypt reasons about:

* SHA-512 → `CatCrypt.Util.Sha512Verified.{maj, ch, bigSigma0, bigSigma1, smallSigma0,
  smallSigma1}` (FIPS 180-4 §4.1.3, on `BitVec 64`).

## What this is — and what it is NOT (honest framing)

This is a **functional-equality** tie, not a security claim.

- Each compile-from-hax leaf proves a *functional-correctness* fact: the artifact emitted by
  the verified compiler computes a closed-form bit-twiddling reference
  (`prog.denote … = <inline rotate/shift/xor/and formula>`).
- This file transports each such denotation onto the **named abstract FIPS spec function** in
  `Sha512Verified`, so that "what the verified compiler emits" is literally "the FIPS function
  the spec layer is written against".
- It does **NOT** establish collision-resistance, PRF, or any SHA-512 security property of the
  emitted code. SHA-512 is an unkeyed compression primitive; there is no CR/PRF claim here,
  only `<emit-form> = <FIPS spec fn>`.

## Carrier note (honest)

The tie is against `CatCrypt.Util.Sha512Verified`, which operates on **`BitVec 64`** — the same
carrier as the compile-from-hax leaves (`compileFromHax (w := 64)`). The codebase also has a
constructive `CatCrypt.Crypto.Primitives.SHA512` whose round functions operate on **`UInt64`**
and are `@[irreducible]`-sealed; we deliberately do **not** tie against that one, because it is a
different carrier (`UInt64`, not `BitVec 64`) and the sealing blocks definitional unfolding. The
`BitVec 64` `Sha512Verified` functions are the appropriate width/carrier match for these leaves.

## §1 the two right-rotate spellings agree (SHA-512, width 64)

The leaves are stated with `BitVec.rotateRight n`; `Sha512Verified.rotr` is the shift-or form
`rotr x k = (x >>> k) ||| (x <<< (64 - k))`. For `k < 64` they coincide — the width-64 analogue
of `CompileFromHaxSha2KeccakTie.rotateRight_eq_rotr`. The σ-functions' logical right shift is
`Sha512Verified.shr x k = x >>> (k : Nat)`, spelled identically to the leaf form.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxSha512Tie

open CatCrypt.Crypto.SecureCompilation.ThirToComFront (inputValuation frontCtxt rW)
open CatCrypt.Crypto.SecureCompilation.CompileFromHax (compileFromHax)
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxSha512
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)

/-! ## §1  The two right-rotate spellings agree (width 64) -/

/-- `BitVec.rotateRight n` equals the shift-or form `Sha512Verified.rotr x n` for `n < 64`.
    Both reduce to `(x >>> n) ||| (x <<< (64 - n))` definitionally
    (`rotateRight = rotateRightAux ∘ (· % 64)`, `n % 64 = n` for `n < 64`). A pure
    `BitVec 64` fact; says nothing about security. The width-64 analogue of the SHA-256
    `rotateRight_eq_rotr`. -/
theorem rotateRight_eq_rotr (x : BitVec 64) {n : Nat} (hn : n < 64) :
    x.rotateRight n = CatCrypt.Util.Sha512Verified.rotr x n := by
  rw [CatCrypt.Util.Sha512Verified.rotr, BitVec.rotateRight, Nat.mod_eq_of_lt hn,
    BitVec.rotateRightAux]

/-! ## §2  The SHA-512 round/schedule references are the same function

Each `*_form_eq_spec` proves the inline closed form the leaf denotes to equals the named FIPS
function in `Sha512Verified`. `Σ₀`/`Σ₁`/`σ₀`/`σ₁` need the rotate-spelling bridge; `Maj`/`Ch`
are spelled identically (`rfl`). -/

/-- The leaf's `Σ₀` inline form equals the FIPS reference `Sha512Verified.bigSigma0`. -/
theorem bigSigma0_form_eq_spec (x : BitVec 64) :
    x.rotateRight 28 ^^^ x.rotateRight 34 ^^^ x.rotateRight 39
      = CatCrypt.Util.Sha512Verified.bigSigma0 x := by
  rw [CatCrypt.Util.Sha512Verified.bigSigma0,
      rotateRight_eq_rotr x (n := 28) (by omega),
      rotateRight_eq_rotr x (n := 34) (by omega),
      rotateRight_eq_rotr x (n := 39) (by omega)]

/-- The leaf's `Σ₁` inline form equals the FIPS reference `Sha512Verified.bigSigma1`. -/
theorem bigSigma1_form_eq_spec (x : BitVec 64) :
    x.rotateRight 14 ^^^ x.rotateRight 18 ^^^ x.rotateRight 41
      = CatCrypt.Util.Sha512Verified.bigSigma1 x := by
  rw [CatCrypt.Util.Sha512Verified.bigSigma1,
      rotateRight_eq_rotr x (n := 14) (by omega),
      rotateRight_eq_rotr x (n := 18) (by omega),
      rotateRight_eq_rotr x (n := 41) (by omega)]

/-- The leaf's `σ₀` inline form equals the FIPS reference `Sha512Verified.smallSigma0`.
    The logical right shift `x >>> 7` is `Sha512Verified.shr x 7` by definition. -/
theorem smallSigma0_form_eq_spec (x : BitVec 64) :
    x.rotateRight 1 ^^^ x.rotateRight 8 ^^^ x >>> (7 : Nat)
      = CatCrypt.Util.Sha512Verified.smallSigma0 x := by
  rw [CatCrypt.Util.Sha512Verified.smallSigma0,
      rotateRight_eq_rotr x (n := 1) (by omega),
      rotateRight_eq_rotr x (n := 8) (by omega),
      CatCrypt.Util.Sha512Verified.shr]

/-- The leaf's `σ₁` inline form equals the FIPS reference `Sha512Verified.smallSigma1`.
    The logical right shift `x >>> 6` is `Sha512Verified.shr x 6` by definition. -/
theorem smallSigma1_form_eq_spec (x : BitVec 64) :
    x.rotateRight 19 ^^^ x.rotateRight 61 ^^^ x >>> (6 : Nat)
      = CatCrypt.Util.Sha512Verified.smallSigma1 x := by
  rw [CatCrypt.Util.Sha512Verified.smallSigma1,
      rotateRight_eq_rotr x (n := 19) (by omega),
      rotateRight_eq_rotr x (n := 61) (by omega),
      CatCrypt.Util.Sha512Verified.shr]

/-- The leaf's `Maj` inline form equals the FIPS reference `Sha512Verified.maj` (identical
    spelling). -/
theorem maj_form_eq_spec (x y z : BitVec 64) :
    (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z) = CatCrypt.Util.Sha512Verified.maj x y z := rfl

/-- The leaf's `Ch` inline form equals the FIPS reference `Sha512Verified.ch` (identical
    spelling). -/
theorem ch_form_eq_spec (x y z : BitVec 64) :
    (x &&& y) ^^^ ((~~~x) &&& z) = CatCrypt.Util.Sha512Verified.ch x y z := rfl

/-! ## §3  Transport the leaf denotations onto the FIPS spec functions

Each `*_emitted_eq_spec` says: the verified compiler emits a program `prog` whose `BitVec 64`
denotation is exactly the named FIPS function `Sha512Verified.*` the spec layer reasons over.
Functional-equality tie — NOT a security statement. -/

/-- The emitted `Σ₀` leaf computes `Sha512Verified.bigSigma0`. -/
theorem bigSigma0_emitted_eq_spec :
    ∃ (prog : Com jasminDialect (frontCtxt 64 1 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 1) ["x"] bigSigma0Src64 = some prog ∧
      ∀ (x : BitVec 64),
        prog.denote (inputValuation 64 1 (fun _ => x))
          = CatCrypt.Util.Sha512Verified.bigSigma0 x := by
  obtain ⟨prog, hc, hden⟩ := bigSigma0_512_compiles
  exact ⟨prog, hc, fun x => (hden x).trans (bigSigma0_form_eq_spec x)⟩

/-- The emitted `Σ₁` leaf computes `Sha512Verified.bigSigma1`. -/
theorem bigSigma1_emitted_eq_spec :
    ∃ (prog : Com jasminDialect (frontCtxt 64 1 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 1) ["x"] bigSigma1Src64 = some prog ∧
      ∀ (x : BitVec 64),
        prog.denote (inputValuation 64 1 (fun _ => x))
          = CatCrypt.Util.Sha512Verified.bigSigma1 x := by
  obtain ⟨prog, hc, hden⟩ := bigSigma1_512_compiles
  exact ⟨prog, hc, fun x => (hden x).trans (bigSigma1_form_eq_spec x)⟩

/-- The emitted `σ₀` leaf computes `Sha512Verified.smallSigma0`. -/
theorem smallSigma0_emitted_eq_spec :
    ∃ (prog : Com jasminDialect (frontCtxt 64 1 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 1) ["x"] sigma0Src64 = some prog ∧
      ∀ (x : BitVec 64),
        prog.denote (inputValuation 64 1 (fun _ => x))
          = CatCrypt.Util.Sha512Verified.smallSigma0 x := by
  obtain ⟨prog, hc, hden⟩ := sigma0_512_compiles
  exact ⟨prog, hc, fun x => (hden x).trans (smallSigma0_form_eq_spec x)⟩

/-- The emitted `σ₁` leaf computes `Sha512Verified.smallSigma1`. -/
theorem smallSigma1_emitted_eq_spec :
    ∃ (prog : Com jasminDialect (frontCtxt 64 1 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 1) ["x"] sigma1Src64 = some prog ∧
      ∀ (x : BitVec 64),
        prog.denote (inputValuation 64 1 (fun _ => x))
          = CatCrypt.Util.Sha512Verified.smallSigma1 x := by
  obtain ⟨prog, hc, hden⟩ := sigma1_512_compiles
  exact ⟨prog, hc, fun x => (hden x).trans (smallSigma1_form_eq_spec x)⟩

/-- The emitted `Maj` leaf computes `Sha512Verified.maj`. -/
theorem maj_emitted_eq_spec :
    ∃ (prog : Com jasminDialect (frontCtxt 64 3 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 3) ["x", "y", "z"] majSrc64 = some prog ∧
      ∀ (x y z : BitVec 64),
        prog.denote (inputValuation 64 3 ![x, y, z])
          = CatCrypt.Util.Sha512Verified.maj x y z := by
  obtain ⟨prog, hc, hden⟩ := maj512_compiles
  exact ⟨prog, hc, fun x y z => (hden x y z).trans (maj_form_eq_spec x y z)⟩

/-- The emitted `Ch` leaf computes `Sha512Verified.ch`. -/
theorem ch_emitted_eq_spec :
    ∃ (prog : Com jasminDialect (frontCtxt 64 3 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 3) ["x", "y", "z"] chSrc64 = some prog ∧
      ∀ (x y z : BitVec 64),
        prog.denote (inputValuation 64 3 ![x, y, z])
          = CatCrypt.Util.Sha512Verified.ch x y z := by
  obtain ⟨prog, hc, hden⟩ := ch512_compiles
  exact ⟨prog, hc, fun x y z => (hden x y z).trans (ch_form_eq_spec x y z)⟩

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxSha512Tie
