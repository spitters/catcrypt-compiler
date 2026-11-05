# mlkem-libjade (vendored)

Pinned copy of the ML-KEM-768 AVX2 Jasmin source of
[mlkem-libjade](https://github.com/pq-code-package/mlkem-libjade), release
`v2025.12.1`, commit `c2380886a0d644266661e702d5000027df095a2b`, under the
Apache License 2.0 (`LICENSE`). Attribution is in `NOTICE`; the statement of
changes required by section 4(b) of the licence is in `MODIFICATIONS.md`.

The upstream repository names no copyright holder. The ML-KEM sources are
committed by Tiago Oliveira and Manuel Barbosa; the upstream `MAINTAINERS.md`
lists Tiago Oliveira, Nigel Jones, Peter Schwabe, Manuel Barbosa and Miguel
Quaresma.

## Files

The files under `src/` and `LICENSE` are copied unmodified from the upstream
commit; the SHA-256 digests below are those of the upstream files and of the
copies.

| Path | Upstream path | SHA-256 |
|---|---|---|
| `src/mlkem768_amd64_avx2/mlkem768_amd64_avx2.jazz` | same | `a5f98a774a01374608e4b147c604b3b8b01961212948dfa4a4fb32ed904c931f` |
| `src/mlkem768_amd64_avx2/api.h` | same | `0074815df5e2e76db7f8bf7270d651faf1659e9204d3fc5728349662a741e04e` |
| `LICENSE` | `LICENSE` | `c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4` |

`NOTICE`, `MODIFICATIONS.md` and this file were written for CatCrypt.

## Use

The `.jinc` importer (`CatCrypt/Crypto/Jasmin/JincInline.lean`) reads
`mlkem768_amd64_avx2.jazz` as a single source unit; the file has no `require`
lines. The importer's output, and the assembly the compiler's backend renders from
it, are derived from this source; `MODIFICATIONS.md` states the changes.

## Updating

Replace the files under `src/` with those of a newer upstream commit, update
the commit, release and digests here and in `NOTICE`, and re-run the
known-answer tests of `catcrypt-mlkem768`.
