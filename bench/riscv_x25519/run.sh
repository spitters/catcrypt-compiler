#!/usr/bin/env bash
# Link the verified RV64 X25519 ladder object into a C driver and check it against
# RFC 7748 under qemu-riscv64. Run `lake exe riscv-x25519-emit` from the package root
# first. Uses a local riscv64-linux-gnu-gcc and qemu-riscv64 when both are on PATH,
# and an ubuntu:24.04 container otherwise.
set -euo pipefail
cd "$(dirname "$0")"
if [ ! -f gen/x25519_ladder.o ]; then
  echo "gen/x25519_ladder.o is missing: run 'lake exe riscv-x25519-emit' from the package root" >&2
  exit 1
fi
build_and_check='riscv64-linux-gnu-gcc -O1 -static -o gen/driver driver.c gen/x25519_ladder.o &&
  python3 check.py qemu-riscv64 gen/driver'
if command -v riscv64-linux-gnu-gcc >/dev/null && command -v qemu-riscv64 >/dev/null; then
  bash -c "$build_and_check"
else
  docker run --rm -v "$PWD":/w -w /w ubuntu:24.04 bash -c "
    apt-get update -qq >/dev/null &&
    apt-get install -y -qq gcc-riscv64-linux-gnu libc6-dev-riscv64-cross qemu-user python3 >/dev/null &&
    export QEMU_LD_PREFIX=/usr/riscv64-linux-gnu &&
    $build_and_check"
fi
