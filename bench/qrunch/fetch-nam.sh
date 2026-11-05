#!/usr/bin/env bash
# Download the Nam arithmetic and Toffoli circuits used by compare.py into bench/qasm/nam/.
#
# The circuits are those of Nam, Ross, Su, Childs and Maslov, "Automated optimization of large
# quantum circuits with continuous parameters" (npj Quantum Information 4, 2018), in the
# OpenQASM 2 form of the VOQC benchmarks (github.com/inQWIRE/VOQC-benchmarks,
# Nam-benchmarks/Arithmetic_and_Toffoli). That repository states no licence, so the files are
# not redistributed here; this script fetches them at a fixed commit. The three largest
# (gf2^128, gf2^131, gf2^163) are left out.
#
#   bench/qrunch/fetch-nam.sh
#   cd bridge && uv run python -I ../bench/qrunch/compare.py --out results-nam.tsv ../bench/qasm/nam/*.qasm
set -euo pipefail

COMMIT=3582e1b7df5a88215905d2f591307214fe965165
BASE="https://raw.githubusercontent.com/inQWIRE/VOQC-benchmarks/$COMMIT/Nam-benchmarks/Arithmetic_and_Toffoli"
OUT="$(cd "$(dirname "$0")/../.." && pwd)/bench/qasm/nam"

FILES=(
  adder_8 barenco_tof_10 barenco_tof_3 barenco_tof_4 barenco_tof_5 csla_mux_3 csum_mux_9
  gf2^10_mult gf2^16_mult gf2^32_mult gf2^4_mult gf2^5_mult gf2^64_mult gf2^6_mult
  gf2^7_mult gf2^8_mult gf2^9_mult mod5_4 mod_adder_1024 mod_mult_55 mod_red_21
  qcla_adder_10 qcla_com_7 qcla_mod_7 rc_adder_6 tof_10 tof_3 tof_4 tof_5 vbe_adder_3
)

mkdir -p "$OUT"
for f in "${FILES[@]}"; do
  curl -fsSL "$BASE/${f//^/%5E}.qasm" -o "$OUT/$f.qasm"
done
echo "${#FILES[@]} circuits in $OUT"
