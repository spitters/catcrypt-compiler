# Statement of modifications (Apache License 2.0, section 4(b))

This statement covers the material in this directory taken from mlkem-libjade
(<https://github.com/pq-code-package/mlkem-libjade>, commit
`c2380886a0d644266661e702d5000027df095a2b`, release `v2025.12.1`).

## Files distributed unmodified

`src/mlkem768_amd64_avx2/mlkem768_amd64_avx2.jazz`,
`src/mlkem768_amd64_avx2/api.h` and `LICENSE` are byte-identical to the
upstream files; their SHA-256 digests are listed in `README.md`. No upstream
file is distributed in modified form.

## Derived works and the changes made

1. Imported programs. The CatCrypt `.jinc` importer parses
   `mlkem768_amd64_avx2.jazz` and partially evaluates each exported function
   into a CatCrypt intermediate program. It inlines every call, folds
   compile-time constants and loop bounds, unrolls loops or keeps them rolled
   over a run-time trip index, drops contract clauses (`requires`, `ensures`),
   annotations (`#[...]`), speculative-load-hardening intrinsics
   (`#init_msf`, `#update_msf`, `#protect`, `#declassify`, which it evaluates
   at their architectural meaning) and spill hints, and renames local
   variables. The imported program is generated at build time and is not
   stored as source.

2. Assembly. The CatCrypt backend compiles the imported program to x86-64
   assembly (`.s`) with its own instruction selection, register allocation
   and stack layout. This assembly is not the output of the Jasmin compiler
   and differs from the upstream file
   `src/mlkem768_amd64_avx2/mlkem768_amd64_avx2.s`, which CatCrypt does not
   distribute.

3. Entry points. The exported functions keep the upstream names and the C
   interface of `api.h`: `jade_kem_mlkem_mlkem768_amd64_avx2_keypair_derand`,
   `_keypair`, `_enc_derand`, `_enc` and `_dec`.

Files carrying derived material are marked with a header naming
mlkem-libjade, the pinned commit and this statement.
