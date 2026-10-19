# `CatCrypt/Tactic/`: domain tactics

Tactics for bignum, tower-field, matrix and distribution goals. Modules are in the
namespace `CatCrypt.Tactic`. Several modules re-export a CatCrypt-core tactic under
this directory's name. [CORRECTNESS.md](../../CORRECTNESS.md) lists the tactics of
the three correctness techniques (descent, ascent, transfer).

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
| [`KernelRfl`](KernelRfl.lean) | `kernel_rfl`, an `Eq` goal closed by `Eq.refl` with the check left to the kernel |
| [`Inv`](Inv.lean), [`InvAttr`](InvAttr.lean) | `inv [f] h` (`with pat`), inversion of `h : f x = some y` or a checker `c x = true`; simp sets `ir_inv` (inversion) and `code_layout` (instruction-list `++`, length, indexing, membership) |
| [`BindAlign`](BindAlign.lean), [`BindVcgen`](BindVcgen.lean), [`EnvSearch`](EnvSearch.lean), [`FieldClear`](FieldClear.lean), [`ProofTermAudit`](ProofTermAudit.lean) | re-exports of `CatCryptCore.Tactics.*` |

The re-exports of the remaining CatCrypt-core tactics are in
[`CatCrypt/Tactics/`](../Tactics/AGENTS.md).

## `kernel_rfl`

Closes a goal `a = b` with `Eq.refl a` and skips the elaborator's
definitional-equality check; the kernel checks `a ≡ b` when the declaration is
added. The goal must be an `Eq` without metavariables. Free variables are allowed
and stay opaque.

Use it for an equation whose two sides agree by evaluation of a closed program
over symbolic inputs, such as the value of a `ScalarStraightRun.runProg` run
against its specification (`FrodoMulAddSa.saBody_run`,
`Secp256k1PointOpPrologue.constInit_run`). There the kernel finishes in under a
second, while `rfl` runs through the elaborator's `isDefEq` and exceeds its
heartbeat budget. Use `rfl` when the elaborator's check is cheap, and
`decide` when the goal is a decidable proposition over closed data.

A wrong equation is reported at the enclosing declaration as a kernel type
mismatch, not at the tactic. In a `module` file the kernel unfolds only exposed
definitions: every definition the evaluation passes through must be in an
`@[expose]` section, and a string built with `toString` or `s!` needs
`import all Init.Data.Repr` in the consuming module.
