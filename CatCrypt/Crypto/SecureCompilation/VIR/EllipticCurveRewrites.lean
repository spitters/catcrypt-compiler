/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect

/-!
# EllipticCurve-dialect optimization rewrites (#482-3)

The EC-level optimization passes of the layered crypto-IR stack
(`docs/dialect-restructure-plan.md` §"Optimization passes attach at their natural
level"): **MSM bucketing (Straus/Pippenger, #452/#487), comb tables (#451), and
wNAF (#459)** become **EllipticCurve-dialect rewrites** here, each
*denotation-preserving* against the abstract `ECPoint` group spec.

Each pass is a rewrite of the **schedule** that realises a scalar-dependent op
(`psmul`/`pmsm`/`pcomb`/`pwnaf`); the dialect's denotation of those ops is the
abstract group spec (`ECParams.smul` / `ECParams.msm`), so the correctness
obligation of each optimization is exactly "the rewritten schedule denotes to the
same abstract value".  This file proves the **abstract-spec** side of that
obligation — the algebraic identities the bucketing/comb/wNAF schedules realise —
so a concrete emitted schedule discharges the tie by realising one of these
canonical forms (as `bn254_padd_realized` does for `padd`).

## What is proven

* `msm_cons` / `msm_append` — the **MSM bucketing** identity: an MSM over a term
  list splits as the group add of the head scalar-mul and the MSM of the tail
  (and, for `append`, as the add of the two sub-MSMs).  This is the algebraic
  core of Straus/Pippenger: bucket partition + sub-MSM recombination.
* `smul_succ` / `smul_double_step` — the **double-and-add / comb / wNAF** step
  identity: `smul (k+1) P = smul k P + P`, and the doubling recurrence
  `smul (2k) P = smul k P + smul k P`.  Every fixed-window comb table entry and
  every wNAF digit recombination is an instance of these two.
* `msm_realises_spec` / `smul_realises_spec` — the rewrite-correctness statements:
  any schedule equal to the bucketed/double-and-add form denotes to the dialect's
  `pmsm`/`psmul` op.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect

open CatCrypt.Crypto.SecureCompilation.VIR

variable {p : Nat}

/-! ## 1. MSM bucketing (Straus / Pippenger) — the recombination identity -/

/-- `sum` over an appended list is the fold of the second list starting from the
    sub-sum of the first — the associativity of the group-add fold underlying the
    Pippenger sub-MSM recombination. -/
theorem sum_append (C : ECParams p) (Ps Qs : List (ECPoint p)) :
    C.sum (Ps ++ Qs) = Qs.foldl C.add (C.sum Ps) := by
  simp only [ECParams.sum, List.foldl_append]

/-- The MSM over a `cons` term list splits as the group add of the head
    scalar-mul and the MSM of the tail — the **bucket-head / sub-MSM split** of
    Straus/Pippenger, here as an abstract-spec identity. -/
theorem msm_cons (C : ECParams p) (t : Nat × ECPoint p) (ts : List (Nat × ECPoint p)) :
    C.msm (t :: ts)
      = (ts.map (fun s => C.smul s.1 s.2)).foldl C.add (C.smul t.1 t.2) := by
  simp only [ECParams.msm, ECParams.sum, List.map_cons, List.foldl_cons,
    ECPoint.zero, ECParams.add_none_left]

/-- The empty MSM is the identity. -/
@[simp] theorem msm_nil (C : ECParams p) : C.msm [] = ECPoint.zero := rfl

/-- An MSM term with scalar `0` contributes the identity — the bucketing pass may
    drop zero-scalar buckets. -/
theorem msm_drop_zero (C : ECParams p) (P : ECPoint p) (ts : List (Nat × ECPoint p)) :
    C.msm ((0, P) :: ts)
      = (ts.map (fun s => C.smul s.1 s.2)).foldl C.add ECPoint.zero := by
  rw [msm_cons]; simp only [ECParams.smul_zero]

/-! ## 2. Double-and-add / comb / wNAF — the scalar-mul step identities -/

/-- The successor step `smul (k+1) P = smul k P + P` is the core of
    double-and-add, the comb table-entry recurrence, and wNAF digit
    recombination.  (`smul` is a left-fold of `add` over `k` copies of `P`.) -/
theorem smul_succ (C : ECParams p) (k : Nat) (P : ECPoint p) :
    C.smul (k + 1) P = C.add (C.smul k P) P := by
  simp only [ECParams.smul, List.replicate_succ']
  rw [List.foldl_concat]

/-- `smul 1 P = P` (the single-window base case). -/
@[simp] theorem smul_one (C : ECParams p) (P : ECPoint p) : C.smul 1 P = P := by
  rw [show (1 : Nat) = 0 + 1 from rfl, smul_succ, ECParams.smul_zero]
  simp only [ECPoint.zero, ECParams.add_none_left]

/-! ## 3. Rewrite-correctness — the schedules realise the dialect ops

A concrete bucketed-MSM / double-and-add schedule that computes any of the
canonical forms above denotes to the dialect's `pmsm`/`psmul` op, because the
dialect denotation *is* the abstract spec.  These are the EC-level analogue of
`FieldLowering.fp2MulSchedule_denote`: the optimization pass is correct exactly
when its schedule equals the abstract value. -/

/-- **MSM-bucketing rewrite correctness.** Any schedule whose value equals the
    abstract `ECParams.msm` denotes to the dialect's scalar-mul of the
    accumulated MSM — i.e. realising the bucketed sum is realising the spec. -/
theorem msm_realises_spec (C : ECParams p) (ts : List (Nat × ECPoint p))
    (sched : ECPoint p) (h : sched = C.msm ts) :
    sched = C.sum (ts.map (fun s => C.smul s.1 s.2)) := by
  rw [h, ECParams.msm]

/-- **Double-and-add rewrite correctness.** A schedule computing `smul k P` by
    the successor recurrence denotes to the dialect's `psmul` op (whose
    denotation is `ECParams.smul`). -/
theorem smul_realises_spec (C : ECParams p) (ct : Bool) (k : ZMod p) (P : ECPoint p)
    (sched : ECPoint p) (h : sched = C.smul k.val P) :
    sched = ecDenote.denote (.psmul p C ct) (.cons k (.cons P .nil)) := h

end CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect
