/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.RelationalFront
public import Mathlib.Data.ZMod.Basic
public import Std.Tactic.BVDecide

/-!
# The relational front's second customer: a non-`id` (injective-not-surjective) encoding

`RelationalFront.lean` lands the seam (`RealizedKernel`) and its first worked
instance `fieldAddRealizedKernel` — but that instance uses `enc = id`, the
*same-representation* regime that trivialises the transport (`map4`/univalence
cap collapses to nothing when the carrier is the spec's own type). It exercises
the IR seam but says nothing about the **encoding** half of the relational front.

This module is the **second customer**, exercising the genuinely interesting
transport path: an encoding `enc` that is **injective but not surjective** — the
exact regime the module docstring of `RelationalFront` flags as the next step
("a non-`id` `enc` instance ... with a serialization"), and the regime *every*
real crypto serialization lives in (most byte strings are not valid field
elements / points).

## The spec and its encoding

* **Spec**: `A = ZMod 251`, `op = (· + ·)` — modular addition in the small prime
  field `F_251` (the GF(251) base field of the MQOM/SDitH Solinas reductions the
  golden path already emits the conditional-subtract reduce for).
* **Encoding**: `enc : ZMod 251 → BitVec 64 := fun a => BitVec.ofNat 64 a.val`,
  the **canonical least-residue representative**. This is
  * **injective**: for `a ≠ a'` in `ZMod 251`, `a.val ≠ a'.val` and both are
    `< 251 < 2^64`, so the 64-bit images differ (`ZMod.val_injective` +
    `BitVec.ofNat` injective on the `< 2^64` range);
  * **NOT surjective**: nothing in the image exceeds `250`, so e.g.
    `BitVec.ofNat 64 251` (let alone `2^63`) has no preimage. The image is the
    `251`-element subset `{0, …, 250}` of the `2^64`-element carrier.

  This is the `map4` level exactly: equality-reflecting embedding, no
  surjectivity, no Type-equivalence — and `EndoOpRealization`'s `enc_inj` is all
  the transport needs.

## The computational operator `bop` and its emitted `Com`

`bop` must satisfy the commuting square `enc (a +_{251} b) = bop (enc a) (enc b)`,
i.e. `bop` must perform the **mod-251 reduction** that the BitVec carrier does not
do for free (plain `fieldAddCom` would compute `enc a + enc b` un-reduced — the
square would FAIL: `BitVec.ofNat 64 ((a.val+b.val) % 251) ≠ enc a + enc b` in
general). So this instance genuinely needs a reducing kernel, not `fieldAddCom`.

We emit `fieldAddMod251Com` (below): `s := a + b; <conditional-subtract-251 on s>`
— `fieldAddCom`'s add followed by the golden-path `fieldCondSub251Com` body. For
operands in `[0,250]` the sum is `≤ 500 ≤ 501`, the range the branch-free
conditional-subtract `(s ≥ 251 ? s-251 : s)` reduces exactly. All ops
(`add`/`regConst`/`sub`/`shrImm`/`and`) are in `SupportedOp`, so the kernel rides
the golden path to AArch64 + RISC-V (+ x86 KAT tier) unchanged, and its
`Com.denote` is a cheap `rfl`.

## What this demonstrates

`spec_eq_transfers_to_emit` instantiated here decides an **abstract `F_251`
equation** (`a + b = a' + b'` in `ZMod 251`) by the emitted machine kernel's
denotation on the *serialized* operands — through an encoding that is injective
and **not** onto. That is the relational front carrying a real serialization,
not the `id` shortcut.

## The `381 → 377` curve note (HONEST)

The bench-D reuse target named in `RelationalFront` is a full curve
`ECParams.add` (`bls12_381 → bls12_377`). That is **not** reached here and needs
more than a field add: `ECParams.add` (i) ranges over `ECPoint = Option (ZMod p
× ZMod p)` (a *sum* type — the encoding must serialize the infinity point and the
affine pair, not a single residue), and (ii) its computational realization is a
whole chord/tangent *schedule* of field ops (one `fInv` + several `fMul`/`fSub`),
i.e. a multi-op `Com` whose `com_denotes_bop` is the field-lowering correctness,
not a one-line `rfl`. This module establishes the injective-not-surjective
*encoding* path on the smallest honest spec (a field add that genuinely reduces);
lifting it to `ECParams.add` reuses this `EndoOpRealization` shape but swaps the
carrier for `Option (ZMod p × ZMod p)` and the kernel for the lowered group-law
schedule — tracked, not done here.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.Bridges.ReprTransfer
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn

/-! ## 1. The reducing kernel: GF(251) modular add as a `Com jasminDialect`

`fieldAddMod251Com` over args `[a, b]`: compute `s := a + b`, then the branch-free
conditional-subtract `(s ≥ 251 ? s - 251 : s)` via the mask idiom
`t := s - 251 ; bit := t >>> 63 ; m := 0 - bit ; r := t + (m & 251)`. Every op is
in `SupportedOp`, so the kernel rides the golden path to both backends. -/

/-- GF(251) modular-add kernel: `s := a + b; condsub251 s`, over `[a, b]`. -/
def fieldAddMod251Com : Com jasminDialect [.reg 64, .reg 64] (.reg 64) :=
  -- s = a + b      (a = .there.here, b = .here  — matches fieldAddCom orientation: x1 + x0)
  .var { op := .regArith .add 64, retTy_eq := rfl,
         args := .cons (.there .here) (.cons .here .nil) }
  -- c251 = 251
  (.var { op := .regConst 64 251, retTy_eq := rfl, args := .nil }
  -- t = s - c251
  (.var { op := .regArith .sub 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- bit = t >>> 63
  (.var { op := .shrImm 64 63, retTy_eq := rfl, args := .cons .here .nil }
  -- c0 = 0
  (.var { op := .regConst 64 0, retTy_eq := rfl, args := .nil }
  -- m = c0 - bit
  (.var { op := .regArith .sub 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there .here) .nil) }
  -- masked = m & c251
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons .here
            (.cons (.there (.there (.there (.there .here)))) .nil) }
  -- r = t + masked
  (.var { op := .regArith .add 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there .here))))
            (.cons .here .nil) }
    (.ret .here))))))))

/-- The kernel is in the supported straight-line fragment (8 ops, all in
    `SupportedOp`: add, regConst, sub, shrImm, regConst, sub, and, add). -/
theorem fieldAddMod251Com_ok : ComOK fieldAddMod251Com := by
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  exact ComOK.var (by supported_op) (ComOK.ret _)

/-- The branch-free conditional-subtract of 251 on a single 64-bit word `s`
    (the mask idiom `(s-251) + ((0 - ((s-251) >>> 63)) & 251)`). For `s ≤ 500`
    this equals `s % 251` (`csub251_eq` below) — exactly the kernel body, applied
    to `s = x1 + x0`. -/
def csub251 (s : BitVec 64) : BitVec 64 :=
  (s - (251 : BitVec 64))
    + (((0 : BitVec 64) - ((s - (251 : BitVec 64)) >>> 63)) &&& (251 : BitVec 64))

/-- **Step 2 — value proof, cheap `rfl`.** The kernel denotes `csub251 (x1 + x0)`
    — the branch-free conditional-subtract of the sum (all-ALU; the mask idiom).
    The `x1 + x0` orientation already matches the `RealizedKernel.bop x1 x0` seam. -/
theorem fieldAddMod251Com_denote (x0 x1 : BitVec 64) :
    Com.denote fieldAddMod251Com (.cons x0 (.cons x1 .nil)) = csub251 (x1 + x0) := rfl

/-! ## 2. The conditional-subtract reduces, for operands in range

The single arithmetic fact behind the commuting square: for a sum word `s ≤ 500`
(every sum of two `F_251` residues is `≤ 500`), the branch-free conditional-
subtract equals the modular reduction `s % 251`. Closed by `bv_decide` once the
range bound is phrased as the BitVec comparison `s ≤ 500#64`. -/

/-- **The conditional-subtract is the modular reduction (in range).** For
    `s ≤ 500`, `csub251 s = s % 251`. The carry-free correctness fact; `bv_decide`
    discharges it from the BitVec range bound. -/
theorem csub251_eq (s : BitVec 64) (h : s ≤ (500 : BitVec 64)) :
    csub251 s = s % (251 : BitVec 64) := by
  unfold csub251; bv_decide

/-! ## 3. The injective-not-surjective encoding and its `EndoOpRealization`

`enc : ZMod 251 → BitVec 64 := fun a => BitVec.ofNat 64 a.val`, the canonical
least-residue representative. Injective (distinct residues are distinct
`< 251 < 2^64` words) but not surjective (image is the 251-element subset
`{0,…,250}`). The commuting square `enc (a + b) = csub251 (enc a + enc b)` is the
heart: it says the *abstract* `F_251` add, serialized, equals the emitted kernel
run on the serialized operands. -/

/-- The canonical-representative encoding `ZMod 251 → BitVec 64`. -/
def encMod251 (a : ZMod 251) : BitVec 64 := BitVec.ofNat 64 a.val

/-- **`encMod251` is injective** (equality-reflecting): distinct residues have
    distinct `val < 251 < 2^64`, so distinct 64-bit images. This is the
    `map4`-level `enc_inj` the transport needs — note it is **not** surjective
    (`BitVec.ofNat 64 251` has no preimage), the genuine injective-not-onto case. -/
theorem encMod251_injective : Function.Injective encMod251 := by
  intro a b hab
  have ha : a.val < 251 := ZMod.val_lt a
  have hb : b.val < 251 := ZMod.val_lt b
  have hv : a.val = b.val := by
    have := congrArg BitVec.toNat hab
    simp only [encMod251, BitVec.toNat_ofNat] at this
    omega
  exact (ZMod.val_injective 251) hv

/-- **The commuting square.** The abstract `F_251` add `a + b`, serialized by
    `encMod251`, equals the emitted kernel's `bop` (`csub251` of the sum) run on
    the serialized operands. Both residues are `< 251`, so their sum is `≤ 500`,
    the range where `csub251` reduces (`csub251_eq`); the result is then
    `(a.val + b.val) % 251 = (a + b).val` (`ZMod.val_add`). -/
theorem encMod251_commutes (a b : ZMod 251) :
    encMod251 (a + b) = csub251 (encMod251 a + encMod251 b) := by
  have ha : a.val < 251 := ZMod.val_lt a
  have hb : b.val < 251 := ZMod.val_lt b
  have hsum : encMod251 a + encMod251 b = BitVec.ofNat 64 (a.val + b.val) := by
    simp only [encMod251]; rw [BitVec.ofNat_add]
  rw [hsum]
  have hlt : a.val + b.val < 2 ^ 64 := by omega
  have h500 : (500 : BitVec 64).toNat = 500 := rfl
  have hle : BitVec.ofNat 64 (a.val + b.val) ≤ (500 : BitVec 64) := by
    apply BitVec.le_def.mpr
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, h500]; omega
  rw [csub251_eq _ hle]
  show encMod251 (a + b) = _
  unfold encMod251
  rw [ZMod.val_add a b]
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_umod, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
      show ((251 : BitVec 64)).toNat = 251 from rfl]
  omega

/-- **The `EndoOpRealization` for `F_251` add via the canonical representative.**
    `op = (· + ·)` on `ZMod 251`; `bop = fun x y => csub251 (x + y)` on
    `BitVec 64`; `enc = encMod251` (injective-not-surjective). This is the
    relational tie — the *non-`id`* second customer of the relational front. -/
def addMod251Realization :
    EndoOpRealization (fun a b : ZMod 251 => a + b)
      (fun x y : BitVec 64 => csub251 (x + y)) where
  enc := encMod251
  enc_inj := encMod251_injective
  commutes := encMod251_commutes

/-! ## 4. The `RealizedKernel`: the abstract `F_251` add, emitted

Tie the realization to the emitted kernel `fieldAddMod251Com`. The seam
`com_denotes_bop` holds because the kernel was built to denote exactly
`csub251 (x1 + x0)` (`fieldAddMod251Com_denote`), and `com_ok` is the supported-
fragment check (`fieldAddMod251Com_ok`). -/

/-- **The relationally-emitted `F_251`-add kernel — the non-`id` second customer.**
    Unlike `fieldAddRealizedKernel` (`enc = id`, same-rep), this kernel carries a
    genuine injective-not-surjective serialization (`encMod251`): its abstract
    source is `ZMod 251` and its computational side is the emitted reducing
    kernel. The encoding half of the relational front is exercised, not trivialised. -/
def addMod251RealizedKernel :
    RealizedKernel (fun a b : ZMod 251 => a + b) where
  bop := fun x y => csub251 (x + y)
  realization := addMod251Realization
  com := fieldAddMod251Com
  com_denotes_bop := fieldAddMod251Com_denote
  com_ok := fieldAddMod251Com_ok

/-! ## 5. The demonstration: an abstract `F_251` equation decided by emitted code

`spec_eq_transfers_to_emit` on this kernel: an abstract `ZMod 251` equation
`a + b = a' + b'` holds **iff** the emitted kernel's `bop` agrees on the
*serialized* (encoded) operands — through the injective-not-surjective
`encMod251`. The two concrete corollaries below are the relational front carrying
a real serialization end-to-end. -/

/-- **The transfer demonstration.** An abstract `F_251` equation `a + b = a' + b'`
    transfers to an equation between the emitted kernel's `bop` on the encoded
    operands. This is `spec_eq_transfers_to_emit` for the non-`id` kernel — the
    relational front deciding an abstract field equation through a real
    (injective-not-onto) serialization. The argument order matches the parent
    `spec_eq_transfers_to_emit` (`a a' b b'`, LHS `op a b = op a' b'`). -/
theorem addMod251_spec_transfers (a a' b b' : ZMod 251) :
    a + b = a' + b' ↔
      csub251 (encMod251 a + encMod251 b) = csub251 (encMod251 a' + encMod251 b') :=
  addMod251RealizedKernel.spec_eq_transfers_to_emit a a' b b'

/-- A concrete *true* instance: `3 + 5 = 1 + 7` in `F_251` is decided by the
    emitted kernel on the serialized operands (both sides reduce to `8`). -/
example :
    csub251 (encMod251 3 + encMod251 5) = csub251 (encMod251 1 + encMod251 7) :=
  (addMod251_spec_transfers 3 1 5 7).mp (by decide)

/-- A concrete *wrap* instance: `200 + 100 = 49 + 0` in `F_251` (the sum `300`
    reduces to `49 = 300 − 251`), decided by the emitted reducing kernel — the
    case plain (non-reducing) `fieldAddCom` would get wrong, so it genuinely
    exercises the serialization's reduction (the encoding is not onto and the
    kernel must perform the mod-251 carry). -/
example :
    csub251 (encMod251 200 + encMod251 100) = csub251 (encMod251 49 + encMod251 0) :=
  (addMod251_spec_transfers 200 49 100 0).mp (by decide)

end CatCrypt.Crypto.SecureCompilation.RelationalFront
