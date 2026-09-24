# `CatCrypt/Tactic/`: domain tactics

Tactics for bignum, tower-field, matrix and distribution goals. Modules are in the
namespace `CatCrypt.Tactic`. Several modules re-export a CatCrypt-core tactic under
this directory's name.

| Module | Tactic or contents |
|---|---|
| [`BignumReason`](BignumReason.lean) | `bignum_reason`, one cascade for bignum obligations; `bignum_bridge`, `bignum_lib`, `bignum_step_trace` |
| [`TowerRing377`](TowerRing377.lean) | `tower_ring_377`, coordinate equalities in the BLS12-377 `Fp6` tower |
| [`ReprTransferAuto`](ReprTransferAuto.lean) | extraction ↔ reference agreement proofs |
| [`MatrixDecide`](MatrixDecide.lean) | `matrix_simp_core`, `matrix_simp_extended`, `matrix_decide` |
| [`NormSqrt`](NormSqrt.lean) | `norm_sqrt` |
| [`SDistrNorm`](SDistrNorm.lean) | `sdistr_norm`, normalization of `SDistr` do-blocks |
| [`Unitarity`](Unitarity.lean) | unitarity of Hermitian involutory exponentials |
| [`Basic`](Basic.lean) | pRHL tactics `rsame`, `rbind`, `rret`, `rsample_same`, `rconseq` |
| [`BindAlign`](BindAlign.lean), [`BindVcgen`](BindVcgen.lean), [`EnvSearch`](EnvSearch.lean), [`FieldClear`](FieldClear.lean), [`ProofTermAudit`](ProofTermAudit.lean) | re-exports of `CatCryptCore.Tactics.*` |

The re-exports of the remaining CatCrypt-core tactics are in
[`CatCrypt/Tactics/`](../Tactics/AGENTS.md).
