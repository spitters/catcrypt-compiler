# catcrypt-mpn

GMP-style multi-precision natural-number (`mpn`) limb operations whose
kernels are emitted by the CatCrypt compiler: the equal-length limb loops
`mpn_{add,sub,and,ior,xor}_n`, the shift funnel `mpn_shift_rt`, the
constant-time comparison `mpn_cmp_ct`, and the schoolbook product
`mpn_mul_basecase_rt`, with safe Rust wrappers and a C ABI over 32-bit or
64-bit digit arrays. The branch `catcrypt-mpn-4.35` of the CatCrypt fork of Lean 4 links the static library
of this crate into its runtime and calls the entries over 32-bit digits.

## Generated vs hand-written

| File | Status |
|------|--------|
| `asm/mpn_*_n_loop_owned.s` | **Generated** — rendered by `MpnCrateEmit.emitMain` (`CatCrypt/Crypto/SecureCompilation/X86Backend/MpnCrateEmit.lean`) from the front-compiled `Lprog`s of `MpnLoopFrontEmit.lean` |
| `obj/mpn_*_n_loop_owned.o` | **Generated** — the byte encoder's objects for the same `Lprog`s, written by `MpnLoopBytesEmit.emitMain` |
| `obj/mpn_{shift_rt,cmp_ct,mul_basecase_rt}_owned.o` | **Generated** — the byte encoder's objects for the front-compiled `Lprog`s of `MpnShiftFrontEmit`, `MpnCmpFrontEmit` and `MpnMulBasecaseFrontEmit`, written by `MpnRuntimeBytesEmit` through `emit_rt_objs.lean` |
| `src/mpn_ffi.rs` | **Generated** — same `#eval`, same `Lprog` values (extern signatures cannot drift from the assembly); printer: `RustAbiPrinter.lean` |
| `src/lib.rs` | Hand-written — crate docs, the extern declarations of the three runtime-trip kernels (`rt_ffi`), the safe seam (`seam`), the C-ABI exports (`cabi`) |
| `build.rs`, `Cargo.toml`, `tests/`, this file | Hand-written |

The emitters write through paths relative to the dev root, the working
directory of every build of the workspace, which reaches this crate as
`../catcrypt-compiler/crates/catcrypt-mpn`. No build runs them: the closing
`#eval emitMain` of `MpnCrateEmit` and of `MpnLoopBytesEmit` is commented out.
Regenerate the files by running those `emitMain`s from the dev root, and the
three runtime-trip objects with
`lake env lean --run ../catcrypt-compiler/crates/catcrypt-mpn/emit_rt_objs.lean`
from the dev root.

## Layers

1. **Kernels** (`obj/*.o`): SysV x86-64, u64 limbs. The equal-length loops
   take `rp=RDI, ap=RSI, bp=RDX, n=RCX`; `add`/`sub` return the carry/borrow
   limb in `RAX`. `mpn_shift_rt(rp, up, n, sh)` sets
   `value(rp[0..=n]) = value(up) * 2^sh + rp[0]` (left shift: `sh = cnt`;
   right shift: `sh = 64 - cnt`, result in `rp[1..=n]`);
   `mpn_cmp_ct(rp, ap, bp, n)` writes `1`, `-1` or `0` to `rp[0]` after a
   full scan; `mpn_mul_basecase_rt(rp, up, vp, un, vn)` writes the product to a
   zeroed `rp` of `un + vn + 1` limbs. The three runtime-trip kernels need
   BMI2 and leave the loop index, not a result, in `RAX`.
2. **Safe kernel API** (`src/mpn_ffi.rs`, generated; `rt_ffi` in `lib.rs`):
   slice wrappers with length and range checks; `unsafe` confined to the
   wrapper bodies.
3. **Seam** (`seam`, safe Rust): the variable-length add/sub bridge, and the
   u32-surface bitwise, compare, shift and multiply operations, which pack
   u32 operands into u64 limbs in a caller-provided scratch slice (a
   `2p`-limb u32 array is the `p`-limb u64 array over the same bytes; odd
   lengths are padded with a zero), call one kernel and unpack.
   Output-length contracts:
   - `lshift_u32(a, k)`: `a.len() + k/32 + 1` limbs, unnormalized;
   - `rshift_u32(a, k)`: `a.len() - k/32` limbs, or none if `k/32 >= a.len()`;
   - `mul_u32(a, b)`: `a.len() + b.len()` limbs, unnormalized, zero if either
     operand is empty;
   - `cmp_u32(a, b)`: `1`/`0`/`-1` on values, lengths may differ.
4. **C ABI** (`cabi`): `mpn_{add,sub}_n_oc_32` (low pairs through the u64
   kernel directly, an odd top limb by a scalar step), and
   `mpn_{and,ior,xor}_n_oc_32`, `mpn_cmp_oc_32`, `mpn_{l,r}shift_oc_32`,
   `mpn_mul_oc_32` over the seam, with scratch on the stack up to 512 u64
   limbs and from `calloc` above; no length bound. `mpn_*_n_oc_64` u64 twins
   and the raw kernel symbols are also in the archive.

## Aliasing

The kernels' verified statements are over distinct arrays; no in-place
(`rp == ap`) contract is verified. The safe API therefore requires distinct
slices (enforced by the borrow checker), and the raw C entries document
non-overlap as a caller obligation.

## Trust boundary

- **Verified in Lean (CatCrypt):** the five equal-length limb loops,
  front-compiled and encoded to object bytes; extern signatures derived from
  the same `Lprog` values. The three runtime-trip kernels are front-compiled
  in `MpnShiftFrontEmit.lean`, `MpnCmpFrontEmit.lean` and
  `MpnMulBasecaseFrontEmit.lean` (see their module docstrings for what is
  proved) and encoded to object bytes by `MpnRuntimeBytesEmit.lean`, which
  `emit_rt_objs.lean` runs as above.
- **Trusted (TCB):** the linker, `rustc` and the glue in this crate (`rt_ffi`, seam,
  C ABI), and the FFI boundary. The seam is differential-tested in
  `tests/kat.rs` and `tests/seam_diff.rs`. The Lean runtime's own glue is
  tested by the harness of the runtime on that branch of the Lean 4 fork.

## Build and test

```
cargo build --release --no-default-features   # the no_std archive
cargo test                                    # KAT and differential tests (default `std` feature)
```

The archive is the `--no-default-features` build: `no_std`
with `panic = "abort"`, so it pulls no Rust std runtime into the final link —
its only undefined symbols are libc `memcpy`/`memset`/`calloc`/`free`/`abort` and the
compiler-rt intrinsics the C toolchain already provides. `cargo test` keeps the
default `std` feature so the KAT harness runs.
