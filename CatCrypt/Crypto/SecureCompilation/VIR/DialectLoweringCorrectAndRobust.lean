/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.ModArithLowering
import CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveLowering
import CatCrypt.Crypto.SecureCompilation.VIR.ParamDialectTransport

/-!
# Algebraic dialect lowerings: functionally correct **and** constant-time, together

`X86Backend/OwnedCorrectAndRobust.ownedCompile_correct_secure_and_CT` states, for
one owned scalar-arith program, **functional correctness** (the machine run
computes the source value) **and** **constant-time robustness** together — but,
as its own docstring records, only for the *owned scalar-arith fragment*
(`List ArithSrc`), naming the algebraic dialect stack (`Field → ModArith → …`)
as the explicit next phase to widen onto.

This file is the **algebraic arm** of that widening. For each algebraic
dialect-stack lowering it pairs the *already-proved* per-level **functional**
(denotation-preservation) theorem with the *already-proved* per-level
**constant-time** (`ctSafe`-preservation) theorem into one capstone conjunction
about the **same** lowering. Nothing here is re-proved: each capstone is a tuple
of existing theorems from `ModArithLowering`, `EllipticCurveLowering`, and the
Param-engine synthesis in `ParamDialectTransport`.

## What each capstone is about, and at what level

* `modArith_lowering_correct_and_robust` — the **ModArith → {Vector | LowCT}**
  (`#442`) lowering. Functional (`lower_denote_preserved`) and CT
  (`lower_ctSafe_preserved`) are **op-level**; we additionally expose the
  **whole-program / `Com`-level** CT statement (`lower_ctSafeCom_preserved`).
  The functional preservation in `ModArithLowering` is op-level only, so the
  whole-program conjunct of this capstone is CT-only (stated as such).
* `ec_lowering_correct_and_robust` — the **EllipticCurve → Field** lowering.
  Functional (`lower_denote_preserved`) and CT (`lower_ctSafe_preserved`) are
  **op-level**, plus the group-law CT statement (`lower_ctSafe_grouplaw`,
  `lower_ctSafe_edwards`). Both preservation theorems in `EllipticCurveLowering`
  are op-level, so this capstone is op-level.
* `field_lowering_correct_and_robust` — the **Field → ModArith** prime-field
  fragment. The **functional** square is discharged by **Trocq's `param_solve`**
  (`ParamDialectTransport.twoOp_lowering_synth` / `threeOp_lowering_synth`), not
  by a hand `cases`/`comp` walk; it is paired with the ModArith op-level CT
  preservation. This conjunct is at the **op-tree (value-realisation)** level —
  the same prime-field, same-carrier fragment on which `param_solve` synthesizes.

## Honest scope

Each capstone composes **dialect-level preservation** facts. This is **not** a
whole-source-to-machine end-to-end statement: the full source→machine chain
links these dialect lowerings through `ModArith → {LowCT | Vector} →` the owned
backend, whose own correct-and-robust anchor is
`X86Backend/OwnedCorrectAndRobust.ownedCompile_correct_secure_and_CT`. What is
stated here is exactly the per-lowering "functional ∧ constant-time" pairing,
at the level (op / whole-program) annotated on each theorem — the algebraic
analogue of the owned-scalar triple, ready to compose onto that anchor.

All goals closed; target axiom set `{propext, Classical.choice, Quot.sound}`. No use
of `jasminc_preserves_ct` (the algebraic lowerings are value-level / bytes-level).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.DialectLoweringCorrectAndRobust

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect
open CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open Transfer

/-! ## 1. ModArith → {Vector | LowCT} : functionally correct ∧ constant-time

The `#442` redundant-limb lowering. We pair op-level denotation preservation
with op-level CT preservation, and additionally expose the whole-program (`Com`)
CT statement. The functional preservation that `ModArithLowering` proves is
op-level (the realisation equals the op's abstract denotation), so the
whole-program conjunct here is CT-only — stated explicitly. -/

/-- **ModArith lowering is functionally correct AND constant-time (op-level).**
    For every `ModArithOp` and any well-typed arguments, the `#442` lowering's
    realisation **computes the op's abstract value** (`lower_denote_preserved`)
    **and** the op together with its chosen route is constant-time
    (`lower_ctSafe_preserved`). Both conjuncts are op-level; the lift to programs
    is by the `Com` structural fold. -/
theorem modArith_lowering_correct_and_robust (op : ModArithOp)
    (args : HVector (fun (t : ModArithTy) => ⟦t⟧)
              (DialectSignature.sig (d := modArithDialect) op)) :
    ModArithDialect.realise op args = modArithDenote.denote op args
      ∧ (op.ctSafe = true ∧ (ModArithDialect.routeOf op).ctSafe = true) :=
  ⟨ModArithDialect.lower_denote_preserved op args,
   ModArithDialect.lower_ctSafe_preserved op⟩

/-- **ModArith lowering preserves constant-time at the whole-program (`Com`)
    level.** For every `Com modArithDialect Γ t`, the source program's
    whole-program CT predicate holds and every op's chosen route is CT
    (`lower_ctSafeCom_preserved`). This is the `Com`-level CT conjunct
    accompanying the op-level functional+CT capstone above (the functional
    preservation that `ModArithLowering` carries is op-level, so the
    whole-program statement is CT-only). -/
theorem modArith_lowering_robust_com {Γ : Ctxt modArithDialect} {t : ModArithTy}
    (c : Com modArithDialect Γ t) :
    ctSafeCom c = true ∧ (∀ op : ModArithOp, (ModArithDialect.routeOf op).ctSafe = true) :=
  ModArithDialect.lower_ctSafeCom_preserved c

/-! ## 2. EllipticCurve → Field : functionally correct ∧ constant-time

The L4→L3 group-law lowering. Both preservation theorems in
`EllipticCurveLowering` are op-level, so this capstone is op-level. We additionally
expose the unconditional group-law CT statements. -/

/-- **EllipticCurve lowering is functionally correct AND constant-time (op-level).**
    For every `ECOp` and any well-typed arguments, the EllipticCurve→Field lowering's
    realisation **computes the op's abstract value** (`lower_denote_preserved`)
    **and** the op is exactly as constant-time as its Field schedule
    (`lower_ctSafe_preserved`): the group-law ops are unconditionally CT, the
    scalar-dependent ops track the `ct` flag. Both conjuncts are op-level. -/
theorem ec_lowering_correct_and_robust (op : ECOp)
    (args : HVector (fun (t : ECTy) => ⟦t⟧)
              (DialectSignature.sig (d := ecDialect) op)) :
    EllipticCurveDialect.realise op args = ecDenote.denote op args
      ∧ op.ctSafe = EllipticCurveDialect.scheduleCtSafe op :=
  ⟨EllipticCurveDialect.lower_denote_preserved op args,
   EllipticCurveDialect.lower_ctSafe_preserved op⟩

/-- **EllipticCurve lowering CT, group law (Weierstrass + twisted-Edwards).** The
    Weierstrass `padd`/`pdbl`/`pmadd`/`pneg` (`lower_ctSafe_grouplaw`) and the
    unified-Edwards `edPadd`/`edPdbl`/`edPsmul`-(ladder) (`lower_ctSafe_edwards`)
    ops lower to a constant-time Field schedule unconditionally — the group-law
    CT conjunct accompanying the op-level correct-and-robust capstone above. -/
theorem ec_lowering_robust_grouplaw {p : Nat} (C : ECParams p) (E : EdwardsParams p) :
    (EllipticCurveDialect.scheduleCtSafe (.padd p C) = true
      ∧ EllipticCurveDialect.scheduleCtSafe (.pdbl p C) = true
      ∧ EllipticCurveDialect.scheduleCtSafe (.pmadd p C) = true
      ∧ EllipticCurveDialect.scheduleCtSafe (.pneg p) = true)
    ∧ (EllipticCurveDialect.scheduleCtSafe (.edPadd p E) = true
      ∧ EllipticCurveDialect.scheduleCtSafe (.edPdbl p E) = true
      ∧ EllipticCurveDialect.scheduleCtSafe (.edPsmul p E true) = true) :=
  ⟨EllipticCurveDialect.lower_ctSafe_grouplaw C,
   EllipticCurveDialect.lower_ctSafe_edwards E⟩

/-! ## 3. Field → ModArith (prime-field) : functionally correct ∧ constant-time

The L3→L2 prime-field fragment. The **functional** square is the one synthesized
by **Trocq's `param_solve`** (`ParamDialectTransport`): an arbitrary prime-field
op-tree lowers to its ModArith op-tree by one engine descent. We pair that
engine-synthesized functional correctness with the ModArith op-level CT
preservation of the corresponding target ops — giving "functionally correct ∧
constant-time" at the op-tree / value-realisation level, on the same prime-field
same-carrier fragment the engine handles. -/

/-- **Field → ModArith (prime-field) is functionally correct AND constant-time.**
    The functional conjunct is the **`param_solve`-synthesized** transport
    (`ParamDialectTransport.twoOp_lowering_synth`): the prime-field op-tree
    `fAddF (fMulF a b) c` lowers to the ModArith op-tree
    `modAddF (modMulF a b) c`, related along the identity encoding on `ZMod p`
    (`Related id …`). The CT conjunct is the ModArith op-level CT preservation of
    the two target ops involved (`modAdd p` and `modMul p`,
    `lower_ctSafe_preserved`). Both are op-tree-level on the prime-field,
    same-carrier fragment. The functional square is discharged by Trocq's
    `param_solve`, not a hand `cases`/`comp` walk. -/
theorem field_lowering_correct_and_robust {p : Nat} (a b c : ZMod p) :
    Related (id : ZMod p → ZMod p)
        (fAddF (fMulF a b) c) (modAddF (modMulF a b) c)
      ∧ ((ModArithOp.modAdd p).ctSafe = true
            ∧ (ModArithDialect.routeOf (.modAdd p)).ctSafe = true)
      ∧ ((ModArithOp.modMul p).ctSafe = true
            ∧ (ModArithDialect.routeOf (.modMul p)).ctSafe = true) :=
  ⟨ParamDialectTransport.twoOp_lowering_synth a b c,
   ModArithDialect.lower_ctSafe_preserved (.modAdd p),
   ModArithDialect.lower_ctSafe_preserved (.modMul p)⟩

/-- **Field → ModArith (prime-field), depth-2 multi-head, functionally correct AND
    constant-time.** Same shape as `field_lowering_correct_and_robust` but on the
    three-head depth-2 op-tree `fAddF (fMulF a b) (fSubF c d)`, with its functional
    square synthesized by `param_solve`
    (`ParamDialectTransport.threeOp_lowering_synth`) and the CT preservation of all
    three target ops (`modAdd`/`modMul`/`modSub`) paired in. -/
theorem field_lowering_correct_and_robust_threeOp {p : Nat} (a b c d : ZMod p) :
    Related (id : ZMod p → ZMod p)
        (fAddF (fMulF a b) (fSubF c d)) (modAddF (modMulF a b) (modSubF c d))
      ∧ ((ModArithOp.modAdd p).ctSafe = true
            ∧ (ModArithDialect.routeOf (.modAdd p)).ctSafe = true)
      ∧ ((ModArithOp.modMul p).ctSafe = true
            ∧ (ModArithDialect.routeOf (.modMul p)).ctSafe = true)
      ∧ ((ModArithOp.modSub p).ctSafe = true
            ∧ (ModArithDialect.routeOf (.modSub p)).ctSafe = true) :=
  ⟨ParamDialectTransport.threeOp_lowering_synth a b c d,
   ModArithDialect.lower_ctSafe_preserved (.modAdd p),
   ModArithDialect.lower_ctSafe_preserved (.modMul p),
   ModArithDialect.lower_ctSafe_preserved (.modSub p)⟩

end CatCrypt.Crypto.SecureCompilation.VIR.DialectLoweringCorrectAndRobust
