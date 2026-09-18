#!/bin/bash
# Reads the printed round-trip program back through the hax frontend.
#
# Run from any directory, after bench/hax_roundtrip/emit_roundtrip.lean has
# written bench/hax_roundtrip/crate/src/lib.rs:
#   1. `cargo hax json` on bench/hax_roundtrip/crate writes
#      hax_frontend_export.json (the THIR of the crate, as JSON);
#   2. bench/hax_roundtrip/read_back.lean reads the body of `roundtrip_prog`
#      with hax-lean's JSON adapter and writes it as a Lean literal to
#      CatCrypt/Crypto/Hax/ImpRustHaxRoundTripExtracted.lean.
# The static check is CatCrypt.Crypto.Hax.ImpRustHaxRoundTrip; build it after
# this script.

set -euo pipefail

# a large hax export overflows the default stack of the JSON reader
ulimit -s unlimited 2>/dev/null || true

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
CRATE="$ROOT/bench/hax_roundtrip/crate"

if [ ! -f "$CRATE/src/lib.rs" ]; then
  echo "missing $CRATE/src/lib.rs: run bench/hax_roundtrip/emit_roundtrip.lean first" >&2
  exit 1
fi

rm -f "$CRATE/hax_frontend_export.json"
(cd "$CRATE" && cargo hax json)

if [ ! -f "$CRATE/hax_frontend_export.json" ]; then
  echo "cargo hax json wrote no $CRATE/hax_frontend_export.json" >&2
  exit 1
fi

cd "$ROOT"
lake env lean --run bench/hax_roundtrip/read_back.lean
