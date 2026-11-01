# BN254 tower under the reg-ptr Jasmin convention

The three Makefiles compile the BN254 tower that AUCurves emits under the
`reg ptr u64[N]` convention with jasminc, and report how much of it lowers to x86-64.
`Makefile` covers the 12-function Fp2 subset and its known-answer test,
`Makefile.241` the 47-function subset through `bn254_Fp12_pow_u`, and `Makefile.259`
the final-exponentiation, Miller-loop and pairing wrappers. Each Makefile header lists
its targets.

## Paths the user sets

- `AUCURVES`: the root of an AUCurves checkout. The Jasmin module read is
  `$(AUCURVES)/bn254-safe-rust/generated/bn254_tower_regptr.jazz`. Every target except
  `clean` stops with an error when it is unset:

  ```sh
  make AUCURVES=/path/to/AUCurves compile-12
  make -f Makefile.241 AUCURVES=/path/to/AUCurves compile-tower
  ```

- `JASMINC`: the jasminc binary, by default the one of the opam switch `rocq-9`.

The `kat` target builds the Rust harness, whose `Cargo.toml` names the
`bn254-safe-rust` crate of the same AUCurves checkout by a relative path; edit that
path when the checkout lies elsewhere.

No default target or CI step of this repository runs this harness.
