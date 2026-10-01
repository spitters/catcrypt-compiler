# RV64 X25519 ladder under qemu

The object `gen/x25519_ladder.o` is `RiscvX25519LadderObject.ladderObject`: an ELF64
relocatable object whose `.text` is the encoding of the 3098-instruction ladder program
of `RiscvX25519LadderBytesProof`, with the function symbol `catcrypt_x25519_ladder`.
`x25519LadderObject_correct` states that this `.text` decodes to a program meeting the
ladder specification. This directory runs the object.

```
lake exe riscv-x25519-emit      # from the package root: writes gen/x25519_ladder.o
bench/riscv_x25519/run.sh       # links driver.c, runs it under qemu-riscv64, checks it
```

`driver.c` fills the 576-byte state block (scalar, `x1 = u`, `x2 = 1`, `z2 = 0`,
`x3 = u`, `z3 = 1`), calls the function and prints `x2` and `z2`. `check.py` forms
`x2 / z2 mod p` and compares it with the RFC 7748 Section 5 algorithm on the three
Section 5.2 vectors and 32 random inputs; it checks its own reference against the
published outputs first.

`run.sh` uses `riscv64-linux-gnu-gcc` and `qemu-riscv64` from `PATH` when both are there,
and an `ubuntu:24.04` container otherwise. It is not run in CI.

The final inversion and the byte encoding of the result are done by `check.py`, not by
the object.
