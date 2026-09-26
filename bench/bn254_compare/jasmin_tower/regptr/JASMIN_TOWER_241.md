# BN254 reg-ptr tower #241 — clearing the partial-region depth limit

Follows #227 (`JASMIN_TOWER_227.md`, unchanged). #227 got the full 53-function
BN254 tower to **type-check** under jasminc and 12 functions to lower to
x86-64; the residual was jasminc's stack-allocation **"the region associated to
variable ... is partial"** constraint on 3-level-nested reg-ptr sub-slices
(Fp12 `x[16:8]` → Fp6 `y[8:8]` → Fp2 element), which blocked Fp6_mul and the
whole deeper graph.

#241 clears that wall (Route 2: restructure the emit so jasminc never sees a
partial sub-slice across a call boundary) and the two further codegen walls it
exposed.

## The three walls and the fixes (AUCurves `Core.v`)

1. **Partial-region on nested reg-ptr sub-slices.**
   `pp_call_tower_staged` now copy-stages **every** pointer argument of a tower
   call (Fp2/Fp6/Fp12/make_line/...) through a disjoint whole-array scratch
   buffer `__sg<w>_<i>` (`stack u64[w]`), the width-`w` generalization of #227's
   leaf-only `__sa` staging. A non-inline callee therefore only ever receives a
   whole `stack u64[w]` buffer, never a partial sub-region of a larger live
   array, so the partial-region check passes. The staging is limb-exact
   (`pp_copyN_in` / `pp_copyN_back`): the callee reads/writes the same words as
   the direct sub-slice call would.

   (A whole-array-skip optimization — stage only genuine partial sub-slices,
   pass whole arrays directly — was tried and *reverted*: it reintroduced the
   partial-region error in the deep Fp12 graph, because a whole `stack u64[8]`
   that has been sliced at offset 4 anywhere — the second Fp of an Fp2 — is
   tracked as partial when passed across a non-inline boundary. Uniform staging
   is required for coverage; the cost is code size.)

2. **x86-64 SysV ABI: > 6 register pointer args.**
   `bn254_Fp12_frobenius_p3` has 8 pointer parameters; the ABI passes only 6 in
   registers. Functions with > 6 pointer params are emitted `inline fn` (no
   register-passing ABI applies to an inlined body); ≤ 6 stay `export fn`.

3. **Variable-amount shift does not lower.**
   `Fp12_pow_u` / `miller_loop` extract bits via `bita = (bita >> i)` with `i`
   a runtime loop counter. The infix form fails jasminc linearization
   (`RCX = RCX >>64u RAX ... Is there an instruction ...?`). The emit now uses
   the `#SHR`/`#SHL` intrinsic (`_,_,_,_,_, x = #SHR(a, i);`) for a non-literal
   count; a literal count keeps the infix immediate-shift form.

## jasminc compile result

- **Type-checking: 53/53** (unchanged from #227).
- **x86-64 codegen: through `bn254_Fp12_pow_u` inclusive — the complete
  Fp2 + Fp6 + Fp12 algebra layer, the Frobenius family (incl. the 8-arg
  `Fp12_frobenius_p3`), `make_line` / `make_line_corrected`, the constant
  loaders, and `Fp12_pow_u` (the hard-exponentiation square-and-multiply
  ladder).** The #227 partial-region wall (Fp6_mul + all Fp12) and the
  variable-shift wall (Fp12_pow_u) are both cleared. `make compile-tower` emits
  the confirmed-compiling subset.

  **47 tower functions** (46 `export fn` + the inlined `Fp12_frobenius_p3`)
  lower to x86-64, up from #227's 12.

See `make compile-tower` for the exact lower-to-`.s` count and
`make typecheck-all` for the 53/53 type-check.

### Residual A: the 6 final-exp / miller / pairing wrappers — register-allocation exhaustion

`final_exp_hard_dsd`, `final_exp_dsd`, `miller_loop[_optimal]`,
`pairing_dsd[_optimal]` (6 functions) **clear the partial-region wall** but hit
a DIFFERENT jasminc limit:

    register allocation: no more free register to allocate variable: out...

These are the largest bodies (`final_exp_hard_dsd` is ~11 k lines after
staging). Uniform call-staging introduces one unrolled `__mv__` limb-move
temporary per copied word — thousands of them in an 11 k-line body — and
jasminc's register allocator runs out of registers / cannot spill them all in
one function. This is the **code-size cost of the staging fix** colliding with
the allocator on the hardest functions, NOT a new semantic or partial-region
wall. The structural lever to clear it is reducing the `__mv__` temporary count
(a `for`-loop copy over the scratch, or a stack-mover, instead of fully
unrolled scalar moves) — follow-on emit work. `make full-attempt` reproduces
the exact allocator dump.

(These 6 are field-blocked on the #219 reg-ptr verified leaves anyway — see
Residual B — so closing the allocator limit does not by itself yield a correct
pairing.)

### Residual B: full-pairing byte-KAT — field-blocked on #219 leaves

The byte-identical **full-pairing KAT** on EIP-196/197 vectors is **not**
delivered here, for a reason orthogonal to #241's codegen work: the emitted
`.jazz` links **structural leaf stubs** (the `inline fn bn254_add/mul/...` are
copy shells, not the verified Montgomery arithmetic — the real AUCurves leaves
use the raw `reg u64` mem-pointer convention and `jasminc` rejects assigning a
`reg ptr u64[4]` to a `reg u64`, the #222 cast error). A field-correct pairing
needs the **#219 reg-ptr verified-leaf re-emit** (the Montgomery leaf bodies
re-emitted with `arr[j]` indexing instead of `[ptr+8*j]`); a reg-ptr-native
leaf compiles (verified empirically), but re-emitting the verified bodies is
separate AUCurves work, explicitly out of #241 scope. Until those leaves are
linked, the pairing's field values are wrong (the stubs only copy), so no
full-pairing byte number is reported — that would be fabricated.

## Faithfulness

`pp_module_regptr_same_inputs` (Qed, #227) is unchanged: both module emitters
are `map _ fs` over one and the same `fs`. #241 additionally **inserts**
limb-move commands (copy-in / copy-out) around each staged call, so it incurs
an observational-equivalence obligation over #227's pure access-syntax
re-spelling. The limb-index correspondence — copy-in then copy-out is the
identity on the source words, and the callee reads/writes the same `w` words it
would under the direct sub-slice call — is documented at
`pp_copyN_index_correspondence` (Core.v). No new `Admitted`.

## Trust delta

For the now-compiling Fp2/Fp6/Fp12 + Frobenius + make_line + Fp12_pow_u layer
(47 functions), the tower arithmetic is native jasmin from the verified
bedrock2 program — no rustc/LLVM, no FFI shim, no cross-object call (leaf calls
are inlined).

The WHOLE pairing leaves rustc/LLVM + the C shim only once **both** residuals
close: Residual A (the 6 final-exp/miller/pairing wrappers' jasminc
register-allocation exhaustion — a `__mv__`-count emit refinement) AND Residual
B (the #219 reg-ptr verified-leaf re-emit, the field-correctness gate). #241
removes the partial-region / ABI / variable-shift codegen blockers on the
tower-composition layer; it does NOT yet deliver the full native pairing, and
no full-pairing byte-KAT number is claimed.
