#!/usr/bin/env bash
# Evaluate the twenty-seven ed25519 part-check statements and fail if any is false.
#
# The correctness of the shipped ed25519_point_add, ed25519_sc_reduce and
# ed25519_sc_muladd rests on part checks closed by `decide +kernel`, which cost
# gigabytes each and do not build on a development box. A re-imported block can make
# a statement false without any build reporting it, because the modules holding the
# checks are not elaborated. This evaluates the same statements with the compiled
# evaluator, from the executor, the models and the part maps alone — none of the
# modules that hold the checks — so it is cheap enough to run early and often. It
# adds no trust: the kernel proofs remain the artefact.
#
# Usage:
#   bash scripts/ed25519-part-check-gate.sh
# Env:
#   PART_CHECK_SKIP_BUILD=1   do not build the gate's closure first (it is already built)
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

if [ "${PART_CHECK_SKIP_BUILD:-0}" != "1" ]; then
  lake build \
    CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedParts \
    CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScMuladdModel
fi

lake env lean scripts/cutgen/Ed25519PartCheckGate.lean
