/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxLeaves
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxKeccak
public import CatCrypt.Crypto.Util.Sha256Verified
public import CatCrypt.Crypto.Primitives.Keccak

/-!
# #607 Phase 3b: DIRECT functional ties — SHA-2 & Keccak compile-from-hax leaves = FIPS spec fns

This module wires the committed **compile-from-hax SHA-256 round-component leaves**
(`CompileFromHaxLeaves.{bigSigma0,bigSigma1,maj,ch}_compiles`) and the committed
**compile-from-hax Keccak leaves**
(`CompileFromHaxKeccak.{chiLane,thetaCLane,thetaDLane}_compiles`) onto the **abstract FIPS
reference functions** the rest of CatCrypt reasons about:

* SHA-256 → `CatCrypt.Util.Sha256Verified.{bigSigma0,bigSigma1,maj,ch}` (FIPS 180-4 §4.1.2);
* Keccak  → `CatCrypt.Crypto.Primitives.Keccak.{chi, theta}` (FIPS 202 §3.2), at a state cell.

## What this is — and what it is NOT (honest framing)

This is a **functional-equality** tie, not a security claim.

- Each compile-from-hax leaf proves a *functional-correctness* fact: the artifact emitted
  by the verified compiler computes a closed-form bit-twiddling reference
  (`prog.denote … = <inline rotate/xor/and formula>`).
- This file transports each such denotation onto the **named abstract FIPS spec function**
  in the protocol/primitive layer, so that "what the verified compiler emits" is literally
  "the FIPS function the spec layer is written against".
- It does **NOT** establish collision-resistance, PRF, or any SHA-256/SHA-3 security
  property of the emitted code. SHA-2/SHA-3 are unkeyed compression/permutation primitives;
  there is no CR/PRF claim here, only `<emit-form> = <FIPS spec fn>`.

These ties are **DIRECT**: the emit-form *is* the FIPS rotate/xor/and spec, up to the
spelling of right-rotate. `Sha256Verified.rotr` is the shift-or form
`rotr x k = (x >>> k) ||| (x <<< (32-k))`; the leaf is stated with `BitVec.rotateRight n`.
They are *definitionally* the same: `BitVec.rotateRight n = rotateRightAux (n % 32)` and
`rotateRightAux m = (· >>> m) ||| (· <<< (32-m))`, so for `n < 32` the two spellings coincide
(`rotateRight_eq_rotr`). The θ left-rotate is the width-64 identity
`rotateLeft 1 = rotateRight 63`. `maj`/`ch`/`χ`/`θ-C` are spelled identically and tie by
reflexivity through the leaf clause.

## Granularity

The tie is at the **round-component** granularity for SHA-256 (the four logical functions
`Σ₀`, `Σ₁`, `Maj`, `Ch` — exactly the leaves committed as compile-from-hax) and at the
**single-step / single-lane** granularity for Keccak (the χ lane, the θ column-parity, and
the θ diffusion lane — exactly the leaves committed as compile-from-hax). For Keccak θ the
two single-lane leaves *compose* into the full per-cell θ output: `thetaCompose_eq_spec`
shows that feeding the θ-C column parities `C[x−1]`, `C[x+1]` into the θ-D leaf and XORing
`a x y` reconstructs `Primitives.Keccak.theta a x y` exactly.

The full SHA-256 round body / message schedule and the full 25-lane Keccak permutation are
*not* committed as single compile-from-hax leaves (those whole-function maps are emitted by
the owned-emit / VIR emitters, a different pipeline), so no whole-permutation functional tie
is claimed here. Each step's emitted leaf scales to the full map by replication over cells,
as documented in the respective leaf files.

## A width note on the χ leaf (honest)

The committed χ leaf `CompileFromHaxKeccak.chiLane_compiles` is at **`w = 32`** (`BitVec 32`),
whereas the FIPS-202 reference `Primitives.Keccak.chi` operates on **`BitVec 64`** lanes. χ is
width-agnostic (only `¬`/`∧`/`⊕`), so the *same* formula is what the 64-bit spec computes:
`chi_spec_eq_form` records `Keccak.chi a x y = a x y ⊕ ((¬ a₁) ∧ a₂)` at width 64, and
`chiLane_emitted_eq_form` ties the (width-32) leaf to that same `a0 ⊕ ((¬a1) ∧ a2)` shape.
We do **not** claim the width-32 leaf equals the width-64 `Keccak.chi` (it cannot, by type);
we tie the leaf to the FIPS χ-lane formula and separately record that `Keccak.chi` is that
formula at width 64.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxSha2KeccakTie

open CatCrypt.Crypto.SecureCompilation.ThirToComFront (inputValuation frontCtxt rW)
open CatCrypt.Crypto.SecureCompilation.CompileFromHax (compileFromHax)
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxLeaves
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxKeccak
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)

/-! ## §1  The two right-rotate spellings agree (SHA-256)

The compile-from-hax leaves are stated with `BitVec.rotateRight n`; the FIPS reference
`CatCrypt.Util.Sha256Verified.rotr` is written with the shift-or form
`rotr x k = (x >>> k) ||| (x <<< (32 - k))`. For the SHA-256 rotation amounts they are equal.
This is the SHA-256 analogue of `CompileFromHaxChachaTie.rotL32_eq_rotateRight`. -/

/-- `BitVec.rotateRight n` equals the shift-or form `Sha256Verified.rotr x n` for `n < 32`.
    Both reduce to `(x >>> n) ||| (x <<< (32 - n))` definitionally
    (`rotateRight = rotateRightAux ∘ (· % 32)`, `n % 32 = n` for `n < 32`). A pure
    `BitVec 32` fact; says nothing about security. -/
theorem rotateRight_eq_rotr (x : BitVec 32) {n : Nat} (hn : n < 32) :
    x.rotateRight n = CatCrypt.Util.Sha256Verified.rotr x n := by
  rw [CatCrypt.Util.Sha256Verified.rotr, BitVec.rotateRight, Nat.mod_eq_of_lt hn,
    BitVec.rotateRightAux]

/-! ## §2  The SHA-256 round-component references are the same function

Each `*_form_eq_spec` proves the inline closed form the leaf denotes to equals the named FIPS
function in `Sha256Verified`. `Σ₀`/`Σ₁` need the rotate-spelling bridge; `Maj`/`Ch` are
spelled identically (`rfl`). -/

/-- The leaf's `Σ₀` inline form equals the FIPS reference `Sha256Verified.bigSigma0`. -/
theorem bigSigma0_form_eq_spec (x : BitVec 32) :
    x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22
      = CatCrypt.Util.Sha256Verified.bigSigma0 x := by
  rw [CatCrypt.Util.Sha256Verified.bigSigma0,
      rotateRight_eq_rotr x (by omega),
      rotateRight_eq_rotr x (n := 13) (by omega),
      rotateRight_eq_rotr x (n := 22) (by omega)]

/-- The leaf's `Σ₁` inline form equals the FIPS reference `Sha256Verified.bigSigma1`. -/
theorem bigSigma1_form_eq_spec (x : BitVec 32) :
    x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25
      = CatCrypt.Util.Sha256Verified.bigSigma1 x := by
  rw [CatCrypt.Util.Sha256Verified.bigSigma1,
      rotateRight_eq_rotr x (n := 6) (by omega),
      rotateRight_eq_rotr x (n := 11) (by omega),
      rotateRight_eq_rotr x (n := 25) (by omega)]

/-- The leaf's `Maj` inline form equals the FIPS reference `Sha256Verified.maj` (identical
    spelling). -/
theorem maj_form_eq_spec (x y z : BitVec 32) :
    (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z) = CatCrypt.Util.Sha256Verified.maj x y z := rfl

/-- The leaf's `Ch` inline form equals the FIPS reference `Sha256Verified.ch` (identical
    spelling). -/
theorem ch_form_eq_spec (x y z : BitVec 32) :
    (x &&& y) ^^^ ((~~~x) &&& z) = CatCrypt.Util.Sha256Verified.ch x y z := rfl

/-! ## §3  SHA-256: transport the leaf denotations onto the FIPS spec functions

Each `*_emitted_eq_spec` says: the verified compiler emits a program `prog` whose `BitVec 32`
denotation is exactly the named FIPS function `Sha256Verified.*` the spec layer reasons over.
Functional-equality tie — NOT a security statement. -/

/-- The emitted `Σ₀` leaf computes `Sha256Verified.bigSigma0`. -/
theorem bigSigma0_emitted_eq_spec :
    ∃ (prog : Com jasminDialect (frontCtxt 32 1 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 1) ["x"] bigSigma0Src = some prog ∧
      ∀ (x : BitVec 32),
        prog.denote (inputValuation 32 1 (fun _ => x))
          = CatCrypt.Util.Sha256Verified.bigSigma0 x := by
  obtain ⟨prog, hc, hden⟩ := bigSigma0_compiles
  exact ⟨prog, hc, fun x => (hden x).trans (bigSigma0_form_eq_spec x)⟩

/-- The emitted `Σ₁` leaf computes `Sha256Verified.bigSigma1`. -/
theorem bigSigma1_emitted_eq_spec :
    ∃ (prog : Com jasminDialect (frontCtxt 32 1 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 1) ["x"] bigSigma1Src = some prog ∧
      ∀ (x : BitVec 32),
        prog.denote (inputValuation 32 1 (fun _ => x))
          = CatCrypt.Util.Sha256Verified.bigSigma1 x := by
  obtain ⟨prog, hc, hden⟩ := bigSigma1_compiles
  exact ⟨prog, hc, fun x => (hden x).trans (bigSigma1_form_eq_spec x)⟩

/-- The emitted `Maj` leaf computes `Sha256Verified.maj`. -/
theorem maj_emitted_eq_spec :
    ∃ (prog : Com jasminDialect (frontCtxt 32 3 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 3) ["x", "y", "z"] majSrc = some prog ∧
      ∀ (x y z : BitVec 32),
        prog.denote (inputValuation 32 3 ![x, y, z])
          = CatCrypt.Util.Sha256Verified.maj x y z := by
  obtain ⟨prog, hc, hden⟩ := maj_compiles
  exact ⟨prog, hc, fun x y z => (hden x y z).trans (maj_form_eq_spec x y z)⟩

/-- The emitted `Ch` leaf computes `Sha256Verified.ch`. -/
theorem ch_emitted_eq_spec :
    ∃ (prog : Com jasminDialect (frontCtxt 32 3 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 3) ["x", "y", "z"] chSrc = some prog ∧
      ∀ (x y z : BitVec 32),
        prog.denote (inputValuation 32 3 ![x, y, z])
          = CatCrypt.Util.Sha256Verified.ch x y z := by
  obtain ⟨prog, hc, hden⟩ := ch_compiles
  exact ⟨prog, hc, fun x y z => (hden x y z).trans (ch_form_eq_spec x y z)⟩

/-! ## §4  Keccak χ: the leaf form is the FIPS-202 χ-lane formula (`Primitives.Keccak.chi`)

The committed χ leaf is at `w = 32`; `Primitives.Keccak.chi` is at `BitVec 64`. χ is
width-agnostic. `chi_spec_eq_form` records that the 64-bit spec computes exactly the χ-lane
formula `a x y ⊕ ((¬ a₁) ∧ a₂)`, and `chiLane_emitted_eq_form` ties the (width-32) leaf to
the same `a0 ⊕ ((¬a1) ∧ a2)` shape. -/

/-- **`Primitives.Keccak.chi` is the FIPS-202 χ-lane formula** at every cell `(x,y)` of a
    state `a`: `chi a x y = a x y ⊕ ((¬ a (x+1) y) ∧ a (x+2) y)` (indices mod 5). The leaf
    computes this same formula (at width 32). -/
theorem chi_spec_eq_form (a : CatCrypt.Crypto.Primitives.Keccak.KState) (x y : Fin 5) :
    CatCrypt.Crypto.Primitives.Keccak.chi a x y
      = a x y
          ^^^ ((~~~ a ⟨(x.val + 1) % 5, by omega⟩ y) &&& a ⟨(x.val + 2) % 5, by omega⟩ y) := by
  unfold CatCrypt.Crypto.Primitives.Keccak.chi
  rfl

/-- **Keccak χ-lane emitted by the verified compiler = the FIPS-202 χ-lane formula.** The
    width-32 χ leaf denotes to `a0 ⊕ ((¬a1) ∧ a2)`, the FIPS-202 χ output lane on its three
    governing lanes — the same formula `Primitives.Keccak.chi` computes at width 64
    (`chi_spec_eq_form`). Functional equality, not a security claim. -/
theorem chiLane_emitted_eq_form :
    ∃ (c : Com jasminDialect (frontCtxt 32 3 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 3) ["a0", "a1", "a2"] chiLaneSrc = some c ∧
      ∀ (a0 a1 a2 : BitVec 32),
        c.denote (inputValuation 32 3 ![a0, a1, a2]) = a0 ^^^ ((~~~a1) &&& a2) :=
  chiLane_compiles

/-! ## §5  Keccak θ: the two leaves compose into `Primitives.Keccak.theta`

`Primitives.Keccak.theta` computes, at cell `(x,y)`, the value
`a x y ⊕ (C[x−1] ⊕ rotl64(C[x+1], 1))` where `C[x] = a x 0 ⊕ … ⊕ a x 4`. The two committed
leaves realize exactly these internals:

* `thetaCLane_compiles` — the 5-input column parity `C[x]`;
* `thetaDLane_compiles` — the diffusion `D = c0 ⊕ rotl64(c1, 1)` (with `rotl64(·,1)` written
  as the width-64 `rotateRight 63`).

`thetaCompose_eq_spec` composes them: XORing `a x y` with the θ-D leaf applied to the θ-C
column parities `C[x−1]`, `C[x+1]` reconstructs `theta a x y`. -/

/-- `rotateLeft 1 = rotateRight 63` on `BitVec 64` — the width-64 identity that matches the
    θ-D leaf's `rotateRight 63` against `theta`'s `rotateLeft 1`. Pure `BitVec 64` fact. -/
theorem rotateLeft_one_eq_rotateRight_63 (x : BitVec 64) :
    x.rotateLeft 1 = x.rotateRight 63 := by bv_decide

/-- **`Primitives.Keccak.theta` per-cell, fully decomposed.** At cell `(x,y)`,
    `theta a x y = a x y ⊕ (C[x−1] ⊕ rotl64(C[x+1], 1))` with each `C[·]` the explicit
    5-lane column parity. This exposes the two internals the committed θ leaves realize. -/
theorem theta_spec_decomp (a : CatCrypt.Crypto.Primitives.Keccak.KState) (x y : Fin 5) :
    CatCrypt.Crypto.Primitives.Keccak.theta a x y
      = a x y
          ^^^ ((a ⟨(x.val + 4) % 5, by omega⟩ 0 ^^^ a ⟨(x.val + 4) % 5, by omega⟩ 1
                  ^^^ a ⟨(x.val + 4) % 5, by omega⟩ 2 ^^^ a ⟨(x.val + 4) % 5, by omega⟩ 3
                  ^^^ a ⟨(x.val + 4) % 5, by omega⟩ 4)
                ^^^ (a ⟨(x.val + 1) % 5, by omega⟩ 0 ^^^ a ⟨(x.val + 1) % 5, by omega⟩ 1
                  ^^^ a ⟨(x.val + 1) % 5, by omega⟩ 2 ^^^ a ⟨(x.val + 1) % 5, by omega⟩ 3
                  ^^^ a ⟨(x.val + 1) % 5, by omega⟩ 4).rotateLeft 1) := by
  unfold CatCrypt.Crypto.Primitives.Keccak.theta
  rfl

/-- **The two committed θ leaves compose to `Primitives.Keccak.theta`.** There exist compiled
    programs `cC` (θ column parity) and `cD` (θ diffusion) emitted by the verified compiler,
    such that for every state `a` and cell `(x,y)`: XORing `a x y` with `cD` applied to the
    two column parities `C[x−1] = cC(a[x−1,·])` and `C[x+1] = cC(a[x+1,·])` reconstructs
    `theta a x y` exactly. This is the genuine compose of the two single-lane compile-from-hax
    leaves onto the FIPS-202 θ step. Functional equality, not a security claim. -/
theorem thetaCompose_eq_spec :
    ∃ (cC : Com jasminDialect (frontCtxt 64 5 []) (rW 64))
      (cD : Com jasminDialect (frontCtxt 64 2 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 5) ["a0", "a1", "a2", "a3", "a4"] thetaCSrc = some cC ∧
      compileFromHax (w := 64) (nIn := 2) ["c0", "c1"] thetaDSrc = some cD ∧
      ∀ (a : CatCrypt.Crypto.Primitives.Keccak.KState) (x y : Fin 5),
        a x y
          ^^^ cD.denote (inputValuation 64 2
                ![ cC.denote (inputValuation 64 5
                     ![ a ⟨(x.val + 4) % 5, by omega⟩ 0, a ⟨(x.val + 4) % 5, by omega⟩ 1,
                        a ⟨(x.val + 4) % 5, by omega⟩ 2, a ⟨(x.val + 4) % 5, by omega⟩ 3,
                        a ⟨(x.val + 4) % 5, by omega⟩ 4 ]),
                   cC.denote (inputValuation 64 5
                     ![ a ⟨(x.val + 1) % 5, by omega⟩ 0, a ⟨(x.val + 1) % 5, by omega⟩ 1,
                        a ⟨(x.val + 1) % 5, by omega⟩ 2, a ⟨(x.val + 1) % 5, by omega⟩ 3,
                        a ⟨(x.val + 1) % 5, by omega⟩ 4 ]) ])
          = CatCrypt.Crypto.Primitives.Keccak.theta a x y := by
  obtain ⟨cC, hcC, hdenC⟩ := thetaCLane_compiles
  obtain ⟨cD, hcD, hdenD⟩ := thetaDLane_compiles
  refine ⟨cC, cD, hcC, hcD, fun a x y => ?_⟩
  rw [theta_spec_decomp a x y, hdenC, hdenC, hdenD, rotateLeft_one_eq_rotateRight_63]

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxSha2KeccakTie
