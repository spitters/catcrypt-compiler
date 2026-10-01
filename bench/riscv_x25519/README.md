# RV64 X25519 under qemu

The object `gen/x25519_ladder.o` is `RiscvX25519LadderObject.ladderObject`: an ELF64
relocatable object whose `.text` is the encoding of the 3098-instruction ladder program
of `RiscvX25519LadderBytesProof`, with the function symbol `catcrypt_x25519_ladder`.
`x25519LadderObject_correct` states that this `.text` decodes to a program meeting the
ladder specification. The object `gen/x25519.o` is `RiscvX25519Object.x25519Object`: the
same program followed by the X25519 block function and the C function of `RiscvX25519Proof`,
4246 instructions, with `catcrypt_x25519` at offset 16852; `x25519Object_correct` states that
its `.text` decodes to a program whose function there maps the 32 bytes at `scalar` and `u`
to RFC 7748 `X25519(k, u)` at `out`. This directory runs both objects.

```
lake exe riscv-x25519-emit      # from the package root: writes gen/x25519_ladder.o, gen/x25519.o
bench/riscv_x25519/run.sh       # links the drivers, runs them under qemu-riscv64, checks them
```

`driver.c` fills the 576-byte state block (scalar, `x1 = u`, `x2 = 1`, `z2 = 0`,
`x3 = u`, `z3 = 1`), calls the function and prints `x2` and `z2`. `check.py` forms
`x2 / z2 mod p` and compares it with the RFC 7748 Section 5 algorithm on the three
Section 5.2 vectors and 32 random inputs; it checks its own reference against the
published outputs first.

`driver_x25519.c` calls `catcrypt_x25519(out, k, u)` on the RFC 7748 byte strings `k` and
`u`, unclamped and unmasked, in 8-byte aligned buffers, with `out` filled with `0xa5`, and
prints the 32 bytes of `out`; `check.py --full` compares them with the reference directly.
The driver also fails if `k` or `u` changed, or if a second call with `out == u` gives
different bytes.

`run.sh` uses `riscv64-linux-gnu-gcc` and `qemu-riscv64` from `PATH` when both are there,
and an `ubuntu:24.04` container otherwise. It is not run in CI.

For the ladder object, the final inversion and the byte encoding of the result are done by
`check.py`; the X25519 object does both itself.

These runs test the objects; the theorems are functional correctness only, and no
constant-time or leakage property of either object is proved.
