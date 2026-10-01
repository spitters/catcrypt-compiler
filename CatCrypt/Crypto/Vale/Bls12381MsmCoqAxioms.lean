/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Vale.Bls12381Msm


@[expose] public section
set_option autoImplicit false

/-!
# BLS12-381 G1 MSM leaf axiom ↔ AUCurves Bedrock2 Coq theorem index

Single-place reference connecting the `Bls12381Msm` leaf denotation to its
discharging AUCurves Rocq/Bedrock2 theorem. Parallel to the
`Bls12381FieldMulCoqAxioms.lean` audit trail.

## Trust basis: the Coq proof (not the generated Rust/Jasmin)

The cited authority is the **Coq theorem**, not any `.rs` / `.jazz` file.

## Axiom → discharging theorem

| Lean object | Status | Discharging AUCurves Rocq theorem |
|---|---|---|
| `bls12381_g1_msm_denote` (`Σ kᵢ · Pᵢ`) | cited (see scope below) | `BLS12_MSM.msm_bls12_ok` (`Qed`), `AUCurves/src/Bedrock/BLS12_MSM.v:8558` |
| `Bls12381G1`, `Bls12381G1.add/zero/smul` | surface | opaque `Type` + operations; no computational content. |

## Exactly what `msm_bls12_ok` proves (do not overstate)

`msm_bls12_ok` (`BLS12_MSM.v:8558`, `Qed`) proves the Bedrock2 Pippenger
program `msm_bls12` (window size `c = 9`, `29` windows, `511` buckets)
satisfies `spec_of_msm_bls12`: its output equals

  `msm_spec_output scalars points`
  `= msm_pippenger G1_F g1_identity g1_add_spec g1_double_spec c num_windows …`

the Gallina **bucket-method reference** (`BLS12_MSM.v:98`). The theorem is
stated inside `Section PippengerSpec` and is parametric over:

* an **abstract** group `(g1_add_spec, g1_double_spec, g1_identity)` over
  `G1_F = F × F × F`, with `Hypothesis`es `g1_add_assoc` / `g1_add_comm` /
  `g1_add_identity_l` / `g1_double_identity` (`BLS12_MSM.v:461–465`);
* the leaf curve operations as **WP-spec hypotheses**
  `CurveAddAliasedOK` / `CurveDoubleInplaceOK` / `StoreZero3OK` over the
  callee environment `functions`.

So the `Qed` establishes: the extracted Pippenger program refines the
bucket-method Gallina reference over any commutative group satisfying the
four group hypotheses, given curve-op callees meeting the stated specs.

## Two residual links between this `Qed` and `Σ kᵢ · Pᵢ`

Both links below are open in-tree: neither is composed into `msm_bls12_ok`,
and the leaf value equation `Σ kᵢ · Pᵢ` is not derived from it.

1. **Bucket method = naive sum — not proved for the bedrock2 reference.**
   The refinement target of `msm_bls12_ok` is `msm_spec_output`
   (`BLS12_MSM.v:526`), which unfolds to the **multi-window** `msm_pippenger`
   (`BLS12_MSM.v:98`): window size `c = 9`, `29` windows, running-sum bucket
   reduction, over an abstract `G1 : Type` with list-of-`Z` scalars. The one
   proof that a Pippenger reference computes the naive `Σ kᵢ · Pᵢ` is
   `MSM_Spec.msm_pippenger_correct` (`Qed`,
   `Commitments/theories/MSM_Spec.v:266`), and it concerns a **different
   function**: a **single-window** mathcomp `msm_pippenger` (`MSM_Spec.v:153`)
   over a `finGroupType`, with a `\prod_(s : 'F_r | s != 0)` bucket reduction
   and `'F_r`-valued scalars, proving `msm_pippenger = msm_spec` where
   `msm_spec scalars points = ∏ᵢ pointsᵢ ^ scalarsᵢ` on a prime-order cyclic
   (hence abelian) group. The two `msm_pippenger` differ in arity, window
   structure, scalar representation, and group type; no in-tree lemma composes
   them. So the naive-sum identity holds only for the single-window mathcomp
   variant, not for the multi-window function `msm_bls12_ok` refines.
   (`BLS12_MSM.v`'s header cites a connecting `WeierstrassBridge`; no such file
   is present.)
2. **Concrete G1 discharge — absent in-tree.** `msm_bls12_ok` is stated inside
   `Section PippengerSpec`, fully parametric over (a) four abstract group
   `Hypothesis`es on `g1_add_spec` / `g1_double_spec` / `g1_identity` —
   `g1_add_assoc`, `g1_add_comm`, `g1_add_identity_l`, `g1_double_identity`
   (`BLS12_MSM.v:461–465`) — and (b) three curve-op WP-spec predicates
   `CurveAddAliasedOK` / `CurveDoubleInplaceOK` / `StoreZero3OK`
   (`BLS12_MSM.v:1142/1165/1181`) on the callee environment. No AUCurves file
   discharges any of these at the verified BLS12-381 G1 Jacobian arithmetic:
   there is neither a `Qed` nor an `Admitted` instantiation. `BLS12_MSM_Check.v`
   only runs `Print Assumptions msm_bls12_ok`, and `BLS12_MSM_Extract.v` only
   plugs concrete callee names (`"curve_add"`, `"curve_double"`,
   `"store_zero"`) into the program term for extraction, which is not a proof
   that the environment meets the OK-specs. The BLS12-381 group-law facts that
   do exist (e.g. the affine Weierstrass `commutative_group` in
   `AUCurves/src/Hacspec/Curve/BlsProof.v`) are over a different representation
   than the `F × F × F` triples of `g1_add_spec` and are not wired in.

**Net.** The leaf value axiom `bls12381_g1_msm_denote` (`Σ kᵢ · Pᵢ`) rests on
the abstract-group, hypothesis-parametric program-equivalence `msm_bls12_ok`.
The naive-sum identity for the multi-window reference (link 1) and the concrete
BLS12-381 discharge of the group + curve-op hypotheses (link 2) are additional
trust deltas, not established in-tree.

## Timing class

Verifier-side MSM with public scalars — the Pippenger bucket schedule is
data-dependent (vartime), which is admissible because the scalars are
public. This leaf makes no constant-time claim.

## Qed provenance caveat

A source audit of `BLS12_MSM.v` finds `58` proofs closing with `Qed` and
zero command-level `Admitted` / `Abort` / `Axiom` / `admit` tactic; the four
leaf WP lemmas `msm_bls12_double_shift_wp` / `_bucket_clear_wp` /
`_distribute_wp` / `_reduce_wp` and `msm_bls12_exec_correct`
(`BLS12_MSM.v:8498`) all end in `Qed`. The residual `Admitted` / `admit`
strings — comments describing L2/L3/L4 as `Admitted`, an "Admitted count is 3"
tally, and `BLS12_MSM_Extract.v`'s "sub-axiom `msm_bls12_exec_correct`" note —
are stale narrative from an earlier development state. `MSM_Spec.v` is likewise
all `Qed` despite its `SKETCH` / `Admitted` header. No compiled `.vo` is
present for either file, so this status is from source inspection, not a fresh
machine recheck.

## Rocq sources (paths)

`AUCurves/` is https://github.com/AU-COBRA/AUCurves and `Commitments/` is
https://github.com/SSProve/Commitments.

* `AUCurves/src/Bedrock/BLS12_MSM.v` — `msm_bls12_ok` (`:8558`),
  `msm_bls12_exec_correct` (`:8498`), multi-window `msm_pippenger` (`:98`),
  `msm_spec_output` (`:526`), group hypotheses (`:461–465`),
  `CurveAddAliasedOK` / `CurveDoubleInplaceOK` / `StoreZero3OK`
  (`:1142` / `:1165` / `:1181`).
* `AUCurves/src/Bedrock/BLS12_MSM_Check.v` — `Print Assumptions
  msm_bls12_ok` (does not discharge the parametric hypotheses).
* `AUCurves/src/Bedrock/BLS12_MSM_Extract.v` — extraction driver
  (`msm_bls12` → Safe Rust `msm` / `bls12_msm_raw`, → Jasmin).
* `Commitments/theories/MSM_Spec.v` — `msm_pippenger_correct` (`:266`),
  `msm_spec` (`:92`, the naive `∏ pᵢ ^ sᵢ` reference).
-/
