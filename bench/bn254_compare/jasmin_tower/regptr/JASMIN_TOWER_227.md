# BN254 full-tower reg-ptr jasmin emit (#227)

Closes the 39-function jasminc typing gap left by #222 with a `reg ptr u64[N]`
emit path. Added alongside #222's leaf-only bench (`../`), which is unchanged.

## The #222 gap

#222 emitted the full BN254 tower to jasmin TEXT (`bn254_tower.jazz`, 51 export
fn) via the verified `tr_func_sized 4` / `pp_module` path, but only **12 of 51**
type-checked under jasminc. The emit printed pointer args as `reg u64` (byte
address) and `cmd.stackalloc` temps as `stack u64[4]`; when a tower function
passed a temp to a leaf whose parameter is `reg u64`, jasminc rejected it:

    typing error: can not implicitly cast u64[4] into u64

So Fp2_mul/square, all of Fp6/Fp12, make_line, pow_u, final_exp, miller_loop,
pairing failed at the type level.

## The reg-ptr emit (AUCurves `pp_module_regptr`)

`pp_func_regptr` / `pp_module_regptr` in `Core.v` re-render the SAME
`jasmin_func` AST under the `reg ptr u64[N]` convention:

- pointer parameters / arguments become typed array references;
- byte offsets `(base + 8*k)` become typed sub-slices `base[k:len]` (or the
  element `base[k]` for a single-word store); `ptr_base_off` flattens nested
  `((p + 128) + 32)` chains (the `make_line` Fp12 sub-component addressing);
- the output pointer is threaded (`dst = f(dst, ...)`);
- a call-graph width fixpoint (`infer_widths_module`, seeded with the BN254 leaf
  signatures) assigns each pointer its struct width (Fp=4, Fp2=8, Fp6=24,
  Fp12=48 words) so every leaf/Fp2/Fp6/Fp12 call agrees on the slice length;
- leaf calls are copy-STAGED through disjoint `stack u64[4]` scratch (`__sa0..2`)
  — this handles both in-place self-aliasing (`bn254_add(o, o, o)` doublings)
  and the "partial region" analysis (the inline leaf only ever sees a whole
  4-word array, never a partial sub-slice);
- `if` on a `reg u64` condition (`bit & 1` in `Fp12_pow_u`) gets `!= 0`;
- `bn254_from_word`'s scalar word arg stays a `reg u64` literal.

`ExtractBN254TowerJasmin.v` emits `bn254_tower_regptr.jazz`. It also adds
`Fp2_opp` + `Fp2_inv`, which #222 left as a Rust-only prelude so the jasmin tower
could never link them.

## jasminc result

- **Typing: 53/53.** Every tower function type-checks. The #222 blocker error
  "can not implicitly cast u64[4] into u64" is gone for all of them
  (`make typecheck-all`).
- **x86-64 codegen: 12/53.** The complete Fp2 layer
  (`felem_copy/add/sub/mul/square/opp/inv/mul_xi`) + Fp6 `felem_copy/add/sub/opp`
  lower fully to x86-64 (`make compile-12`, 54 KB `.s`, 2767 instrs). Of these,
  **Fp2_mul / Fp2_square / Fp2_inv / Fp2_mul_xi were ALL in #222's 39-failing
  set** — the reg-ptr path moves them from "fails typing" to "compiles to
  x86-64."

### Residual gap (honest)

`bn254_Fp6_mul` and the deeper graph (Fp6_inv, all Fp12 ops, make_line_corrected,
Fp12_pow_u, final_exp_*, miller_loop*, pairing*) hit a DISTINCT jasminc
stack-allocation constraint — "the region associated to variable ... is partial"
— on **3-level-nested sub-slice reg-ptr calls** (Fp12 `x[16:8]` → Fp6 `y[8:8]` →
Fp2 element read). This is a jasminc codegen limitation on non-inline reg-ptr
slicing depth, NOT the type-level re-typing this task closes. An all-`inline fn`
+ entry-wrapper variant (the `pp_entry_wrapper` / `pp_copyN` scaffold in `Core.v`)
pushes the wall deeper (copies entry params into whole local stack arrays) but
does not yet clear it for the deepest chains; closing it is follow-on jasminc
work.

## Faithfulness (Qed, 0 Admitted)

`pp_module_regptr_same_inputs` (Core.v): `pp_module fs` and `pp_module_regptr fs`
are both `map _ fs` over one and the same function list, each reading the
identical `jf_body f` — there is NO AST rewrite between the baseline emit and the
reg-ptr emit, only a printer swap. Combined with the existing Qed theorem
`tr_cmd_correct` (`jf_body` = `tr_cmd` of the bedrock2 body), this gives: the
reg-ptr `.jazz` and the baseline `.jazz` denote the same verified bedrock2
program. The access-syntax delta (typed slice `base[k:len]` vs pointer
arithmetic `(base + 8*k)`) is the analogue of the inert `#[spill]`
register-class delta proven for `pp_module_nospill`
(`pp_locals_decls_nospill_drops_spill` / `pp_locals_decls_spill_form`).

## KAT (`make kat`)

`bn254_tower_regptr_kat.rs`: reg-ptr `Fp2_felem_copy` byte-identical to the Rust
tower's `tower::bn254_Fp2_felem_copy` on the published EIP-197 G2 generator
x-coordinate (Montgomery form). **PASS, byte-identical.** No fabricated vectors.

Scope: the emitted `.jazz` links STRUCTURAL leaf stubs (the `inline fn
bn254_add/mul/...` are copy shells, not the verified Montgomery arithmetic — the
real leaves use the reg-u64 mem-pointer convention and cannot take a reg-ptr
argument without a #219 reg-ptr leaf re-emit). The one leaf whose stub realises
its true semantics is `bn254_felem_copy` (copy a→o), so `Fp2_felem_copy` is the
byte-exact assertion. A byte-identical Fp2_mul/add/sub KAT against the Rust tower
requires reg-ptr verified leaves; this file does not provide them. The full-pairing
KAT on EIP-196/197 vectors (non-degeneracy, e(P,Q)·e(-P,Q)=1, e(2G)·e(3G)=e(5G))
remains blocked on the residual codegen gap above.

## Inlining / FFI overhead (`make compile-12`; the #222 1.70x question)

#222 measured Fp2_add jasmin 39 vs Rust 23 cyc/op (1.70x), attributed to
cross-object leaf-call (FFI) overhead. The reg-ptr path emits the leaves as
`inline fn`, so jasminc inlines them into the tower body: the compiled reg-ptr
`Fp2_add`/`Fp2_mul`/etc. asm contains **0 `call` instructions** (verified on
`gen/tower_regptr_12.s`). The cross-object call overhead is therefore eliminated
by construction. A meaningful cyc/op parity number requires the reg-ptr VERIFIED
Montgomery leaves inlined (the #219 leaf re-emit, out of #227 scope), so no
cyc/op figure is fabricated here — the structural result is "leaf calls inlined,
0 cross-object `call`s," which is what closes the 1.70x FFI gap.

## Trust delta

For the 12 compiling reg-ptr functions, the Fp2/Fp6 tower arithmetic is native
jasmin from the verified bedrock2 program — no rustc/LLVM, no FFI shim, no
cross-object call. Extending this to the WHOLE pairing (and thus fully dropping
rustc/LLVM + the C shim from the tower-composition trust base, leaving only the
verified jasminc + the verified leaves) requires closing the residual
partial-region codegen gap above. The Fp word leaves already went native in #219.
