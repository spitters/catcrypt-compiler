/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn

/-!
# Variable-distance shift: the one primitive the emit alphabet cannot yet reach

A *variable-distance* shift shifts a register by **another register's value**
(`a >>> b.toNat` / `a <<< b.toNat`), not by a compile-time immediate. The
`jasminDialect` already models it: `JasminBinOp.shr` / `.shl` are the logical
shifts by `b.toNat` (`JasminDialect.lean`, lines 122–130), denoted as the
`regArith .shr 64` / `regArith .shl 64` ops over two register operands `[a, b]`.

So at the **dialect-semantics level** the variable shift is fully available, and
this file proves it: the one-op `Com`s `varShrCom` / `varShlCom` denote exactly
`a >>> b.toNat` / `a <<< b.toNat` by `rfl` (§1). This is genuine — the dialect's
`JasminBinOp.apply` reduces structurally to the BitVec shift.

## What is NOT yet available: the emit path (§2, documented gap)

A variable shift **cannot ride the golden path** (`com_arm_e2e` /
`com_riscv_e2e`). The reason is structural, not incidental:

* `SupportedOp` (`ScalarLinDeBruijn.lean`) lists `add/sub/mul/and/or/xor`,
  `mulhi`, the *immediate* shifts `shrImm`/`shlImm`, and `regConst`. The
  *variable* shifts `regArith .shr` / `regArith .shl` are deliberately **absent**.
* `opToStmts` (`ScalarLinFront.lean`) has a `RegStmt` for every supported op, but
  its catch-all `_ => []` swallows `regArith .shr` / `.shl` — there is **no
  `RegStmt`** for a register-amount shift (the `RegStmt` alphabet `ScalarLin.lean`
  has only immediate `shrI`/`shlI`).

Consequently a `Com` containing `regArith .shr 64` is *not* `ComOK`, so
`comToReg_faithful` says nothing about it and the two backend e2e theorems do not
apply. We do **not** edit `SupportedOp` / `RegStmt` / the front. Instead §2
records precisely what a real backend extension would need:

1. a new neutral statement `RegStmt.shrV dst a b` / `RegStmt.shlV dst a b` (a
   register-amount shift, dst from two register sources);
2. its ARM lowering `lsrv` / `lslv` (variable-amount logical shifts) and its
   RISC-V lowering `srl` / `sll` (register-form, not the `i` immediate form),
   each with a `select_correct` `rfl`-class proof;
3. an `opToStmts` arm `regArith .shr _ => [.shrV …]` + a `SupportedOp`/`ComOK`
   clause + the matching `opToStmts_*_correct` op-lemma (binary, same shape as
   `opToStmts_bin_correct`).

## The constant-time caveat (§2)

A variable shift **by a secret amount is not constant-time on many cores**: the
timing of a barrel shifter is data-independent on most modern 64-bit cores, but
several microarchitectures (and essentially all small/embedded cores) implement a
variable shift as a data-dependent loop, leaking the *amount*. So a register-amount
shift must be gated to **public** shift amounts: the CT analysis (the
`JasminCTByConstruction` / `thirDialect` CT layer) must classify a variable shift's
*amount operand* as a public input and **reject** a shift whose amount is
secret-derived — exactly as it already rejects a secret array index (the only
other amount-as-data surface). This is why the immediate shifts `shrImm`/`shlImm`
are unconditionally CT (the amount is a compile-time constant, never data) and are
the ones the front emits today.

## The genuine workaround for the bounded-public case (§3)

When the shift amount is **public and bounded to a small fixed set** (the common
case — e.g. a rotate distance fixed by the cipher, or a 0..3 lane selector), the
variable shift **is** expressible branchlessly in the *existing* alphabet, by a
**select-tree of immediate shifts**: nest the dialect's constant-time `select`
over the `shrImm`-by-each-candidate results. §3 proves, for amount `b ∈ {0,1,2,3}`
(`b.toNat < 4`), that such a 2-level select-tree of `shrImm`s denotes exactly
`a >>> b.toNat` — by `interval_cases` over the bounded cases. This is constant-time by
construction (every immediate shift is evaluated; the selects are branch-free) and
needs **no backend extension** — it rides the existing `select` + `shrImm`
emit path. It is the right answer whenever the amount set is small and public; the
full register-amount op (§2) is only needed for an unbounded public amount.

## Summary of what is proven here

* `varShrCom_denote` / `varShlCom_denote` — the dialect-level variable shift
  denotes `a >>> b.toNat` / `a <<< b.toNat` (`rfl`).
* `varShr_not_supported` / `varShl_not_supported` — the variable-shift op is **not**
  `SupportedOp` (so the emit gap is a theorem, not a comment).
* `boundedVarShr_denote` — the bounded-public variable right shift (amount `< 4`)
  equals the immediate-shift select-tree, `interval_cases` over the 4 cases.

No `sorry`, no new `axiom`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VarShift

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.ScalarLin
open CatCrypt.Crypto.SecureCompilation.ScalarLinFront
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn

/-! ## 1. The variable-distance shift at the dialect level (genuine semantics)

The register-amount shift exists in the dialect: `regArith .shr 64` /
`regArith .shl 64` over two register operands `[a, b]` shift `a` by `b.toNat`.
The one-op `Com`s below denote exactly that, by `rfl`. -/

/-- **Variable right shift.** `a >>> b.toNat` as a one-op `Com jasminDialect` over
    args `[a, b]` — `regArith .shr 64`, the register-amount logical right shift
    (`v2 := a >> b; ret v2`). The shift amount is the *second register* `b`, not an
    immediate. -/
def varShrCom : Com jasminDialect [.reg 64, .reg 64] (.reg 64) :=
  .var { op := .regArith .shr 64, retTy_eq := rfl,
         args := .cons (.there .here) (.cons .here .nil) }
    (.ret .here)

/-- **Variable left shift.** `a <<< b.toNat` as a one-op `Com jasminDialect` over
    args `[a, b]` — `regArith .shl 64`, the register-amount logical left shift. -/
def varShlCom : Com jasminDialect [.reg 64, .reg 64] (.reg 64) :=
  .var { op := .regArith .shl 64, retTy_eq := rfl,
         args := .cons (.there .here) (.cons .here .nil) }
    (.ret .here)

/-- **Dialect-level value, cheap `rfl`.** The variable right-shift source denotes
    `a >>> b.toNat` — `JasminBinOp.apply .shr` reduces structurally to `>>> .toNat`.
    (`x0` is the second arg `b`, `x1` the first arg `a`, by the de-Bruijn order, so
    the value is `x1 >>> x0.toNat`.) -/
theorem varShrCom_denote (x0 x1 : BitVec 64) :
    Com.denote varShrCom (.cons x0 (.cons x1 .nil)) = x1 >>> x0.toNat := rfl

/-- **Dialect-level value, cheap `rfl`.** The variable left-shift source denotes
    `a <<< b.toNat`. -/
theorem varShlCom_denote (x0 x1 : BitVec 64) :
    Com.denote varShlCom (.cons x0 (.cons x1 .nil)) = x1 <<< x0.toNat := rfl

/-! ## 2. The emit gap: variable shift is *not* `SupportedOp`

The golden-path emit (`com_arm_e2e` / `com_riscv_e2e`) only fires for ops in
`SupportedOp`. The two theorems below prove the variable shifts are excluded — so
the gap documented in the module header is a *theorem*, not a comment. The fix
(new `RegStmt.shrV`/`shlV` + ARM `lsrv`/`lslv` + RISC-V `srl`/`sll` + an
`opToStmts`/`SupportedOp`/`ComOK` clause + a binary op-lemma) plus the CT caveat
(secret-amount shifts must be rejected; gate to public amounts) are spelled out in
the module docstring. -/

/-- **The emit gap as a theorem (right shift).** `regArith .shr 64` — the
    variable-distance right shift — is **not** in `SupportedOp`, so it cannot ride
    `comToReg_faithful` / `com_arm_e2e` / `com_riscv_e2e`. (Closing the emit gap is
    a backend extension; see the module docstring §2.) -/
theorem varShr_not_supported : ¬ SupportedOp (JasminOp.regArith .shr 64) := by
  rintro (⟨bop, heq, hb⟩ | heq | ⟨k, heq | heq⟩ | ⟨k, heq⟩) <;>
    first
    | (simp only [JasminOp.regArith.injEq] at heq; rcases heq with ⟨rfl, _⟩;
       rcases hb with h | h | h | h | h | h <;> cases h)
    | exact JasminOp.noConfusion heq

/-- **The emit gap as a theorem (left shift).** `regArith .shl 64` is likewise not
    `SupportedOp`. -/
theorem varShl_not_supported : ¬ SupportedOp (JasminOp.regArith .shl 64) := by
  rintro (⟨bop, heq, hb⟩ | heq | ⟨k, heq | heq⟩ | ⟨k, heq⟩) <;>
    first
    | (simp only [JasminOp.regArith.injEq] at heq; rcases heq with ⟨rfl, _⟩;
       rcases hb with h | h | h | h | h | h <;> cases h)
    | exact JasminOp.noConfusion heq

/-! ## 3. The bounded-public workaround: a select-tree of immediate shifts

For a **public** amount bounded to `{0,1,2,3}`, the variable shift IS branchless
in the existing alphabet. The reference value is the 2-level constant-time
select-tree over the four immediate-shift results — `select` and `shrImm` are both
already `SupportedOp`, so this rides the existing emit path with no extension. The
theorem proves the select-tree equals `a >>> b.toNat` whenever `b.toNat < 4`, by
`bv_decide` over the bounded cases.

The tree (with `bit i = i`-th bit of `b`, `cond = 1#1` selecting the *first*
argument per `selectW`):

    selectW b₁  (selectW b₀ (a>>>3) (a>>>2))   -- high bit set ⇒ amount 2 or 3
                (selectW b₀ (a>>>1) (a>>>0))   -- high bit clear ⇒ amount 0 or 1

where `b₀ = b & 1` and `b₁ = (b >>> 1) & 1` (as `reg 1` conditions). -/

/-- The constant-time select-tree of immediate right shifts realising a variable
    right shift for a **public, bounded** amount (`b.toNat ∈ {0,1,2,3}`). Built
    from the dialect's CT `selectW` over the four `>>>`-by-constant results; both
    `select` and `shrImm` are already `SupportedOp`. The conditions are the low two
    bits of `b`, packaged as `reg 1`. -/
def boundedShrTree (a b : BitVec 64) : BitVec 64 :=
  let b0 : BitVec 1 := BitVec.ofNat 1 b.toNat          -- low bit of b
  let b1 : BitVec 1 := BitVec.ofNat 1 (b.toNat >>> 1)  -- next bit of b
  selectW b1 (selectW b0 (a >>> 3) (a >>> 2))
             (selectW b0 (a >>> 1) (a >>> 0))

/-- **The bounded-public workaround, proven.** For a public amount `b.toNat < 4`,
    the immediate-shift select-tree denotes exactly the variable right shift
    `a >>> b.toNat`. Constant-time by construction (every immediate shift is
    evaluated; the selects are branch-free) and needs no backend extension — it
    rides the existing `select` + `shrImm` emit path. By `interval_cases` over the
    bounded cases. -/
theorem boundedVarShr_denote (a b : BitVec 64) (hb : b.toNat < 4) :
    boundedShrTree a b = a >>> b.toNat := by
  simp only [boundedShrTree, selectW]
  -- The amount is one of 0,1,2,3; case on b and discharge each.
  interval_cases h : b.toNat <;> simp_all

end CatCrypt.Crypto.SecureCompilation.VarShift
