# BN254 full-tower jasmin extraction (#222)

Extract the FULL BN254 pairing tower (Fp2/Fp6/Fp12 + miller_loop + final_exp +
pairing) to a single native jasmin module, so the tower-composition layer leaves
the rustc/LLVM trust base. The win is TRUST/composition, not speed (#219 settled
that the ~7.6x perf gap is algorithmic).

## Emit

AUCurves `src/Bedrock/ExtractBN254TowerJasmin.v` runs the SAME bedrock2
`bn254_tower_funcs` list that `ExtractSafeTower.v` emits as the Rust `tower`
module — through the verified `tr_func_sized 4` / `polish_func` / `pp_module`
path (the convention `BN254_OptimizedOps.v` already uses for struct-passing
Fp12 functions). Outputs:

- `bn254-safe-rust/generated/bn254_tower.jazz`         (spill emit, 51 export fn)
- `bn254-safe-rust/generated/bn254_tower_nospill.jazz` (no-spill, same 51, drops
  the 11 `#[spill]` hints)

All 51 tower functions emit to jasmin text: Fp2/Fp6/Fp12 arithmetic, Frobenius,
make_line(_corrected), the seven constant loaders, Fp12_pow_u, final_exp_dsd /
final_exp_hard_dsd, miller_loop(_optimal), pairing_dsd(_optimal).

## Faithfulness

- `Core.tr_cmd_correct : forall c, cmd_jasmin_equiv c (tr_cmd c)` (Qed) — the
  bedrock2 `cmd` -> `jasmin_cmd` translation is faithful. Every tower body is
  `cmd.call`/`cmd.stackalloc`/`cmd.set`/`cmd.store`/`cmd.cond`/`cmd.while`, all
  covered by `tr_cmd`. The jasmin tower and the Rust `tower` module are two
  pretty-prints of one verified bedrock2 program.
- `Core.pp_locals_decls_nospill_drops_spill` / `pp_locals_decls_spill_form`
  (Qed) — the spill vs no-spill emits differ ONLY in the `#[spill]`
  register-class hint (an inert jasminc allocation hint). The two `.jazz` files
  denote the same program. The committed pair differs in exactly the 11
  `#[spill]` occurrences.
- Representation: the tower funcs inline no field multiply (they only move and
  call leaves), so the radix / MULX concern is confined to the Fp leaves. The
  tower emit is representation-agnostic. Residual obligation beyond register
  class: NONE for the tower layer — the only AST nodes are calls, moves,
  stackallocs, and the pow_u loop, all in `cmd_jasmin_equiv`.

KAT (`bn254_tower_kat.rs`): the jasminc-accepted subset (Fp2_add / Fp2_sub /
Fp2_felem_copy, compiled against the verified leaves) is BYTE-IDENTICAL to the
Rust tower's `tower::bn254_Fp2_{add,sub,felem_copy}` on the published EIP-197 G2
generator coordinates (Montgomery form). 4/4 PASS. No fabricated vectors.

## Honest gap: 12 compile, 39 don't (calling convention)

The bedrock2->jasmin emit prints pointer arguments as `reg u64` (integer
address; byte-offset addressing `(out + 32)`) and `cmd.stackalloc` temporaries
as `stack u64[N]` (jasmin arrays). When a tower function passes a stackalloc'd
Fp/Fp2/... temporary to a leaf whose parameter is `reg u64`, jasminc rejects it:

    typing error: can not implicitly cast u64[4] into u64

Minimal repro (`reg u64` convention fails; `reg ptr u64[N]` convention compiles):

    export fn leaf_add(reg u64 o, reg u64 a, reg u64 b) { ... }
    export fn caller(reg u64 out, reg u64 x) {
      stack u64[4] v0;
      leaf_add(v0, x, x);   // <-- u64[4] cannot decay to reg u64
    }

This never surfaced for the standalone leaves (`bn254_leaves.jazz`): they take
`reg u64` params and never CALL a `reg u64`-param function with a stack array.
The tower is the first emit that does, exposing the convention gap.

Partition (of the 51):

- **12 compile as-is** (no stackalloc passed to a call): `bn254_Fp2_felem_copy`,
  `bn254_Fp2_add`, `bn254_Fp2_sub`, `bn254_Fp2_conjugate`, `bn254_Fp2_mul_fp`,
  and the seven constant loaders (`bn254_load_gamma1`, `_gamma2`, `_w_frob_c1`,
  `_gamma1_p2`, `_gamma2_p2`, `_w_frob_p2_c1`, `_q1_y_const`). Verified to
  jasminc -> x86-64 against the leaves (`make compile`).
- **39 hit the gap** (use a stackalloc temporary or call another tower func):
  `bn254_Fp2_mul`, `bn254_Fp2_square`, `bn254_Fp2_mul_xi`, all Fp6 ops, all Fp12
  ops, `bn254_Fp6_mul_fp2`, `bn254_Fp6/Fp12_frobenius*`, `bn254_make_line(_corrected)`,
  `bn254_Fp12_pow_u`, `bn254_final_exp_dsd`/`_hard_dsd`, `bn254_miller_loop(_optimal)`,
  `bn254_pairing_dsd(_optimal)`.

### Closing it (out of #222 scope: a new emit path, not a reuse)

The fix is a `reg ptr u64[N]` emit convention: change `pp_type (JTptr n)` from
`"reg u64"` to `"reg ptr u64[" ++ n ++ "]"`, emit array-indexed access instead
of byte-offset pointer arithmetic, thread leaf return values
(`v0 = leaf(v0, ...)`), and re-type the leaf signatures to match. That re-derives
the emit path and re-validates the leaves — outside the #222 brief of reusing
the #218/#219 `Core.v` primitives. (The `reg ptr u64[N]` convention is exactly
what the CatCrypt bench stub leaves in `../bn254_leaves.jinc` use and what
compiles in the minimal repro above.)

## Bench (parity, MIN-of-3, core-pinned)

`bn254_tower_bench.rs` (`make bench`, `$(PIN)=taskset -c 2`):

    BN254 Fp2_add (MIN-of-3, cyc/op):
      jasmin tower : 39
      Rust tower   : 23
      ratio j/r    : 1.70x

The gap is FFI/call overhead (the jasmin Fp2_add makes two cross-object
`bn254_add` leaf calls; the Rust tower inlines), not algorithmic — consistent
with #222 (trust win, not speed).

## Trust delta achieved

- For the 12 compiling functions: the tower-composition arithmetic is native
  jasmin from the verified bedrock2 program — no rustc/LLVM, no FFI shim.
- For the whole tower: the emit + the `tr_cmd_correct` / `pp_locals_decls_*`
  faithfulness lemmas establish that ONE verified bedrock2 program denotes both
  the Rust `tower` module and `bn254_tower.jazz`. Once the 39-function
  convention gap is closed, the entire tower compiles native, removing
  rustc/LLVM + the C shim from the trust base for the whole pairing (leaving
  only jasminc, which is verified). The Fp leaves already went native in #219.
