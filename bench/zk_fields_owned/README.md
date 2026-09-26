# Goldilocks, Poseidon2 and BN254 Poseidon kernels on the owned x86-64 backend

`CatCrypt.Crypto.SecureCompilation.Algebraic.ZkFieldsEmitMain` (`lake exe
zkfieldsowned`) renders seven kernels through `Com.toLprogPhysAbi` and the owned
printer, without jasminc, to `gen/*.s`. The C programs here test the assembled
output against references that do not come from this repository.

## Producing the assembly

The executable is run from the SSProve-lean dev root, which is the single build
root of the workspace:

```sh
make gen            # = cd ../../../SSProve-lean && lake exe zkfieldsowned $PWD/gen
```

With no argument the executable writes to
`../catcrypt-compiler/bench/zk_fields_owned/gen`, relative to the dev root. It exits
with status 1 when a rendered file contains an `UNHANDLED` marker.

## Kernels and ABI

Every kernel is `void f(uint64_t *out, const uint64_t *in)` under the SysV ABI and
uses BMI1 (`andn`).

| file                   | symbol              | `in`                                  | `out`                  |
|------------------------|---------------------|---------------------------------------|------------------------|
| `gl_add.s`             | `gl_add`            | `in[0] = x`, `in[1] = y`, both `< p`  | `out[0] = x + y mod p` |
| `gl_sub.s`             | `gl_sub`            | as above                              | `out[0] = x - y mod p` |
| `gl_mul.s`             | `gl_mul`            | as above                              | `out[0] = x * y mod p` |
| `gl_neg.s`             | `gl_neg`            | `in[0] = x < p`                       | `out[0] = -x mod p`    |
| `poseidon2_kb.s`       | `poseidon2_kb`      | `in[0..15]`, canonical KoalaBear lanes | `out[0..15]`          |
| `poseidon2_m31.s`      | `poseidon2_m31`     | `in[0..15]`, canonical Mersenne-31 lanes | `out[0..15]`        |
| `poseidon_bn254_t3.s`  | `poseidon_bn254_t3` | `in[4k..4k+3]`, lane `k` in Montgomery form | `out[4k..4k+3]`, same form |

* Goldilocks: `p = 2^64 - 2^32 + 1`; results are canonical.
* Poseidon2: one lane per 64-bit word, lane `i` at `in[i]`; KoalaBear
  `p = 2^31 - 2^24 + 1`, Mersenne-31 `p = 2^31 - 1`.
* BN254 Poseidon: circomlib width 3 (`x^5`, 8 full and 57 partial rounds) over
  `r = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001`. Lane
  `k` is stored as the Montgomery form `x * 2^256 mod r`, four little-endian 64-bit
  limbs, least significant first. `poseidon([a, b])` is lane 0 of the permutation
  of `(0, a, b)`.

## Known-answer tests

```sh
make kat            # all four
make kat-gl         # 1,000,000 random pairs plus 18 edge values x 18 edge values
                    # and edge x random, each op vs unsigned __int128 % p
make kat-kb         # Plonky3 0.5.4 test_default_koalabear_poseidon2_width_16
make kat-m31        # Plonky3 0.5.4 test_default_mersenne31_poseidon2_width_16
make kat-bn254      # perm(0,1,2), all three lanes (Poseidon reference
                    # poseidonperm_x5_254_3; lane 0 = circomlibjs poseidon([1,2]))
                    # and lane 0 of perm(0,3,4) (circomlibjs poseidon([3,4]))
```

The Poseidon2 vectors are those of the `#kat` checks in
`CatCrypt/Crypto/Hash/Poseidon2/{KoalaBear,Mersenne31}.lean`. The BN254 harness
converts to Montgomery form by 256 modular doublings and back by 256 modular
halvings, independent of the kernel's Montgomery reduction, and checks that every
output lane is below `r`.

## What is proved

The source programs carry all-input value theorems: `Goldilocks.glAddBlk_value`,
`glSubBlk_value`, `glMulBlk_value`, `glNegBlk_value`;
`Poseidon2KoalaBear.permJasminAt_spec`; `Poseidon2Mersenne31.permJasminAt_spec`;
`PoseidonBN254Lower.permJasminAt_denote`. The physical export, the optimisation
passes and the printer are not proved to preserve them; these tests check the
assembled result on the vectors above.
