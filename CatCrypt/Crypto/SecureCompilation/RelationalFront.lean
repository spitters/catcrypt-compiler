/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Bridges.ReprTransfer
import CatCrypt.Crypto.Bridges.ReprTransferExpr
import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath

/-!
# The relational-compilation front-end (entry point / contract)

This module is the **entry point of the second source→IR ingestion route** for
the CatCrypt verified compiler — the *relational* front that sits next to hax.
Where hax parses Rust *syntax* into `Com` (`compileFromHax`'s narrow-ANF path and
`haxToLowCT`'s loops+arrays path), the relational front transports an **abstract
source specification** (a Lean function / algebraic crypto operation) to an
**emitted realization** via parametricity / representation transport, reusing the
proof-transfer layer `Bridges/ReprTransfer*` and the user's Trocq `Param` engine.

Both fronts feed the **one** `Com` IR and the **one** golden-path backend
(`comToReg_faithful` → AArch64 / RISC-V; `compileComToElf` → x86 ELF).

## The route (concrete chain)

```
  abstract spec  op : A → A → A      (e.g. ECParams.add, a field/group law)
        │   choose an encoding enc : A → α   (α = the BitVec/byte carrier)
        │   prove the commuting square  enc (op a b) = bop (enc a) (enc b)
        ▼
  EndoOpRealization op bop           (Bridges/ReprTransferExpr.lean)  ── relational tie
        │   OpExpr.denote_commutes / expr_eq_transfer  (abstraction theorem:
        │      the single-op square lifts to whole composite terms, for free)
        ▼
  bop is a `Com jasminDialect Γ τ`'s denotation                       ── the IR seam
        │   ComOK + (Com.denote = bop)   [the golden-path Step-1/Step-2 obligations]
        ▼
  comToReg_faithful  ⇒  AArch64 + RISC-V machine code
  compileComToElf    ⇒  x86 ELF `.o` bytes (KAT-gated tier)            ── the backend
```

The **left half** (spec → `EndoOpRealization` → composite transfer) is the
existing, fully-proved `Bridges/ReprTransfer*` content. The **right half** (a
`bop` that is the denotation of an emitted `Com`) is the existing golden path
(`FieldEmitGoldenPath`). This module supplies the **missing connective**: the
`RealizedKernel` record that *names the seam between them* — the obligation that
the realization's computational operator `bop` is exactly what an emitted `Com`
computes — turning the proof-transfer layer into a compilation front.

## hax vs relational — when to use which

* **hax**: there is an existing Rust crate / `haxpipeT` extraction. Ingestion is
  syntactic; the spec is whatever the Rust says. (AEAD, hashes, the libcrux
  primitives.)
* **relational**: there is **no Rust source**, only an abstract algebraic spec —
  field arithmetic, curve group laws, ZK pairing/MSM checks. The "source" is a
  Lean `def` (`ECParams.add`, a `ZMod p` op); transport it to the emitted
  byte/`BitVec` kernel via the encoding. This is the route for *new curves and
  fields*: a new prime `p` is a new `ECParams p` with the **same** group-law
  defs, so the **same** `EndoOpRealization`/`OpExpr` transfer instance ports
  with only the carrier `(enc, bop)` re-pointed — the bench-D `bls12_381 →
  bls12_377` reuse is exactly this (`ECParams` is parametric over `p`; only the
  modulus changes, the realization structure is reused verbatim).

## The cap (HONEST): `map4` / no univalence

Type-level univalence is **inconsistent** in this Lean (`propext` is the safe
Prop-level analogue). So relational transport here is bounded to the
**embedding** level: `enc` is injective (equality-reflecting) but **not**
required surjective — crypto serializations are injective-not-onto (most byte
strings are not valid points). This forbids transporting along a *Type
equivalence* (`A ≃ α`) in general; it permits exactly the **byte-bijection /
equality-reflection** transport `BinOpRealization`/`EndoOpRealization` use
(`map4` in Trocq's hierarchy: the level that needs neither surjectivity nor
univalence). Decidable-equation transfer in both directions is reachable;
full Type-equivalence transport is not, and is not needed.

## Status

The realization-and-transfer half is proved (in `Bridges/ReprTransfer*`). The
two seam obligations that make this a *compilation* front — `bop` is an emitted
`Com`'s denotation (`com_denotes_bop`), and that `Com` is in the supported
fragment (`com_ok`) — are first-class fields of the `RealizedKernel` record.
The worked `fieldAddRealizedKernel` instance below discharges both against the
golden path: `com_denotes_bop := FieldEmitGoldenPath.fieldAddCom_denote` and
`com_ok := FieldEmitGoldenPath.fieldAddCom_ok`. The instance is fully proved,
so the relational front is wired end-to-end through the verified backend.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.Bridges.ReprTransfer
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn

universe u

/-! ## The seam: a relationally-emitted kernel

A `RealizedKernel` ties three things that already exist separately:

1. an abstract source spec `op : A → A → A` (the relational *source* — a Lean
   crypto operation, no Rust);
2. a computational operator `bop : BitVec w → BitVec w → BitVec w` and an
   `EndoOpRealization op bop` (the *relational tie* — `Bridges/ReprTransferExpr`);
3. an emitted `Com jasminDialect [reg w, reg w] (reg w)` whose denotation **is**
   `bop` (the *IR seam* — what the golden path then lowers to machine code).

Field (3) is the only genuinely new obligation: it asserts the realization's
computational side is not a stand-alone Lean function but the artifact the
verified compiler emits. -/

/-- A **relationally-emitted kernel**: an abstract crypto operation `op`, its
    byte-level realization `bop`, the realization tie, and an emitted `Com`
    whose denotation is `bop`. The denotation seam (`com_denotes_bop`) is the
    proof obligation that promotes a `Bridges/ReprTransfer` realization into a
    front-end for the verified compiler. -/
structure RealizedKernel {A : Type} (op : A → A → A) where
  /-- The byte-level computational operator the abstract `op` is realized by.
      Width fixed to 64 — the supported (`AllReg64`) golden-path fragment. -/
  bop : BitVec 64 → BitVec 64 → BitVec 64
  /-- The relational tie (encoding + injectivity + commuting square). This is
      the `Bridges/ReprTransferExpr` payload — supplied, not reproved. -/
  realization : EndoOpRealization op bop
  /-- The emitted source program (what the golden-path backend lowers). -/
  com : Com jasminDialect ([.reg 64, .reg 64] : Ctxt jasminDialect) (.reg 64)
  /-- **The IR seam (proof obligation).** The emitted `Com` denotes exactly the
      realization's computational operator: running `com` on inputs `(x0, x1)`
      computes `bop x1 x0`. Discharged per kernel by a golden-path
      `*_denote`-style `rfl`. -/
  com_denotes_bop :
    ∀ x0 x1 : BitVec 64,
      Com.denote com (.cons x0 (.cons x1 .nil)) = bop x1 x0
  /-- **The supported-fragment obligation.** The emitted `Com` is in the
      straight-line fragment the backend accepts, so `comToReg_faithful` /
      `compileComToElf` apply unchanged. -/
  com_ok : ComOK com

namespace RealizedKernel
variable {A : Type} {op : A → A → A}

/-- **The relational-front transfer-to-emit corollary.** For a relationally
    emitted kernel, an abstract source equation `op a b = op a' b'` transfers to
    an equation between the *emitted* `Com`'s denotations on the encoded
    operands. This is the composite of the realization transfer
    (`EndoOpRealization`/`OpExpr.expr_eq_transfer`) with the IR seam
    (`com_denotes_bop`): the security-level abstract equation is decided by the
    code the verified compiler emits.

    PROOF OBLIGATION (to discharge against `Bridges/ReprTransferExpr`): rewrite
    by `com_denotes_bop` to reduce to `R.realization.commutes` + injectivity,
    i.e. the `eq_transfer` shape already proved on `EndoOpRealization`. -/
theorem spec_eq_transfers_to_emit (R : RealizedKernel op) (a a' b b' : A) :
    op a b = op a' b' ↔
      R.bop (R.realization.enc a) (R.realization.enc b)
        = R.bop (R.realization.enc a') (R.realization.enc b') := by
  -- The single-op commuting square + injectivity is exactly `expr_eq_transfer`
  -- specialized to one binary node (same proof shape as `ReprTransferExpr`).
  rw [← R.realization.commutes, ← R.realization.commutes]
  exact ⟨fun h => by rw [h], fun h => R.realization.enc_inj h⟩

end RealizedKernel

/-! ## Worked instance shape (the field-add kernel, relationally)

The canonical first instance reuses the golden-path `fieldAddCom`
(`FieldEmitGoldenPath`) as the emitted `Com`, with the abstract source being the
`BitVec 64` add itself (`enc = id`, the same-representation regime of
`ReprTransferCompute`). A *genuine* relational instance (e.g. `ECParams.add`
over `ZMod p` with a serialization `enc`) follows the same `RealizedKernel`
shape; only `A`, `op`, `bop`, and `realization` change — and across curves only
the carrier and modulus change, the structure is reused (bench-D `381 → 377`). -/

/-- The same-representation field-add realization: `op = bop = (· + ·)` on
    `BitVec 64`, `enc = id`. The relational tie is trivial here (it becomes a
    `@[csimp]`-style identity, per `ReprTransferCompute`); the *point* is that
    its emitted `Com` is the golden-path `fieldAddCom`, so this instance is fully
    end-to-end through the verified backend.

    PROOF OBLIGATIONS:
    * `realization`: `enc = id`, `commutes := fun _ _ => rfl` (same rep).
    * `com := FieldEmitGoldenPath.fieldAddCom`.
    * `com_denotes_bop`: `FieldEmitGoldenPath.fieldAddCom_denote` (note the
      `x1 + x0` orientation already matches `bop x1 x0`).
    * `com_ok`: `FieldEmitGoldenPath.fieldAddCom_ok`. -/
noncomputable def fieldAddRealizedKernel :
    RealizedKernel (fun a b : BitVec 64 => a + b) where
  bop := fun a b => a + b
  realization :=
    { enc := id, enc_inj := Function.injective_id, commutes := fun _ _ => rfl }
  com := FieldEmitGoldenPath.fieldAddCom
  com_denotes_bop := FieldEmitGoldenPath.fieldAddCom_denote
  com_ok := FieldEmitGoldenPath.fieldAddCom_ok

end CatCrypt.Crypto.SecureCompilation.RelationalFront
