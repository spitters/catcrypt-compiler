# Goldilocks field multiply: pass-selected multi-term reduce vs Plonky3

Head-to-head for the Goldilocks base-field multiply

    goldilocks_mul(x, y) = (x · y) mod (2^64 − 2^32 + 1),

a single 64-bit field element, emitted by the in-Lean x86 backend (MULX, no
jasminc). This is the application of the **multi-term** Solinas
modular-reduction selection pass (`ModReduceSelect`) to the Plonky3 64-bit field.

## The reduce is the verified multi-term `multiSolinasReduce`

Goldilocks `p = 2^64 − 2^32 + 1`, i.e. `c = 2^32 − 1`. The emitted reduce of the
128-bit product `(phi:plo)` is the faithful instruction realisation of
`multiSolinasReduce multiGoldilocks phi plo` (fold count `fuel = 2`):

* `fold1 = phi·c + plo`  → `(a1:a0)`  (MULX by `c`, ADD/ADC);
* `fold2 = a1·c + a0`    → `(b1:b0)`  (`b1 ≤ 1`);
* two conditional subtracts of `p` on the 65-bit `(b1:b0)` (2-word SUB/SBB +
  CMOVB), landing the result in `[0, p)`.

The value-level correctness is the general theorem
`multiSolinasReduce_eq_mod` (axioms `[propext, Quot.sound]`), specialised by
`reduceGoldilocks_eq_mod` (side condition `boundM multiGoldilocks 2 ≤ 2`,
`3·c < 2^64`, discharged by `native_decide`):

    multiSolinasReduce multiGoldilocks high low = (high·2^64 + low) % (2^64 − 2^32 + 1).

Unlike the single-`c` 2^k-boundary reduce of Curve25519/secp256k1 (`§7`/`§8.1`
of `ModReduceSelect`), the multi-term reduce iterates the fold `fuel` times; for
Goldilocks two folds suffice.

## References

| Reference | Symbol | What |
|-----------|--------|------|
| Plonky3 / winterfell | `ref_reduce128` | the `GoldilocksField` reduce128 (the canonical Goldilocks reduce used by the Plonky3 prover), in portable C |
| GMP | `mpz` | `(x·y) mod p`, the canonical-arithmetic oracle |

Plonky3's reduce128 returns a value in `[0, 2^64)` that is reduced but not
necessarily canonical (`< p`); the harness canonicalizes it with one extra
conditional subtract for the byte-equality KAT (the lean kernel already produces
the canonical residue via its two conditional subtracts).

## KAT discipline

`goldilocks_mul_compare.c` byte-equality-gates `lean == Plonky3-ref == GMP mod p`
over fixed corner cases (zeros, one, `p−1`, `p`, `p+1`, `2^32`, max, and products
straddling the conditional subtracts) plus 200 000 xorshift-random pairs. The
bench runs only if all KATs pass. No fabricated vectors.

## Result (taskset -c 3, min-of-5, data-dependent latency chain)

    lean  : ~13.6 cyc/op   (verified fold-fold-2condsub reduce)
    ref   : ~9.5  cyc/op   (Plonky3 reduce128)
    ratio lean/ref : ~1.43x

The reference is faster: Plonky3's reduce128 is a tighter single-pass 32-bit
split, whereas the emitted kernel realises the verified `multiSolinasReduce`
fold-for-fold (two MULX folds + a 2-word double conditional subtract), giving a
longer latency chain. This is the scheduling/representation gap, not a
correctness gap — the residue is byte-identical to GMP. cyc/op figures assume a
~3.5 GHz pin and are latency-bound (the accumulator chain serialises each mul).

## Build / run

    make            # build the compare binary
    make run        # KAT + bench (pinned to core 3)
    make TRIALS=5000000 run
    make emit       # re-emit the .s from the verified Lean AST (from repo root)
    make kat        # KAT only (gate)
