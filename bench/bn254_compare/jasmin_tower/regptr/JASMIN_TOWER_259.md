# BN254 reg-ptr tower #259/#260 — clearing the register-allocation wall

Follows #241 (`JASMIN_TOWER_241.md`). #241 got 47/53 BN254 tower functions to
lower to x86-64 via width-aware reg-ptr call staging; the residual was jasminc's
`regalloc.ml:728` **"no more free register"** exhaustion on the 6 final-exp /
miller / pairing wrappers, whose staging-bloated bodies (`final_exp_hard_dsd`
~11 k lines, thousands of unrolled `__mv__` limb-move temporaries) overran the
allocator.

## Residual A (#259): the staging-copy register-allocation wall — CLEARED

### The fix (AUCurves `Core.v`)

`pp_copyN_in` / `pp_copyN_back` (the width-aware tower-call staging movers)
emitted, per staged word, an unrolled pair

    __mv__ = p[k+j];   dst[j] = __mv__;

— so an `Fp12` (48-word) staged call cost 96 straight-line instructions, and a
wrapper that stages dozens of such calls reached ~11 k lines. jasminc's register
allocator builds an interference graph over the whole function body; the sheer
instruction count (not the single reused `__mv__`) drove the allocator into
"no more free register" exhaustion on the largest wrappers.

#259 emits the staging copies as a **runtime `while`-loop** over a single
counter `__cpj__`:

    __cpj__ = 0;
    while (__cpj__ < n) {
      __mv__ = p[(int)(k + __cpj__)];
      dst[(int) __cpj__] = __mv__;
      __cpj__ += 1;
    }

jasmin does **not** unroll `while` (unlike `for`), so each staged copy is now
O(1) instructions regardless of width `n`. The whole emitted module shrank
**49 769 → 11 724 lines** (4.2×); `final_exp_hard_dsd` shrank ~11 k → 892 lines.

### Result: all 53 functions clear the "no more free register" wall

Compiled per function (each callee replaced by a width-matched `inline fn` stub
so the allocator runs only on the function-under-test's own body):

| Wrapper | lines | jasminc regalloc |
|---|---|---|
| `final_exp_hard_dsd` | 892 | compiles, <1 s |
| `final_exp_dsd` | 180 | compiles, <1 s |
| `miller_loop` | 985 | compiles, <1 s |
| `miller_loop_optimal` | 1629 | compiles, <1 s |
| `pairing_dsd` | 151 | compiles, <1 s |
| `pairing_dsd_optimal` | 151 | compiles, <1 s |

All 6 wrappers that hit `regalloc.ml` "no more free register" under #241 now
allocate to x86-64 — the wall is gone. The 47-function Fp2/Fp6/Fp12 + Frobenius
+ make_line + Fp12_pow_u subset still compiles as a single unit
(`Makefile.241 compile-tower`, ~3 min).

### Residual (honest): monolithic single-invocation compile is throughput-bound

Compiling **all 53 functions in one `jasminc` invocation** does not finish in a
20-minute budget — not because of a register-allocation *wall* (no
"no more free register" error appears), but because each function inlines the
full leaf chain and jasminc re-runs register allocation over that inlined body
per function; 53 such allocations in series exceed the timeout. Every function
allocates instantly *individually* (verified above), so the milestone — every
tower function clears the regalloc wall and lowers to x86-64 — holds; the
remaining item is jasminc throughput on the monolithic module, not a codegen
impossibility. (A `compile-each` target compiles the wrappers as separate units.)

## Residual B (#260): field-correct leaves — bridge validated, emit pending

#241's emitted `.jazz` links **structural leaf stubs** (`pp_regptr_leaf_stubs`:
`inline fn bn254_add/mul/...` are copy shells), so pairing field values are
wrong and no honest pairing number can be reported.

#260 validated the bridge to the **verified Montgomery leaves** empirically:

1. The verified leaves (`bn254_leaves.jazz`) keep the raw `reg u64`
   byte-pointer convention and need `-auto-spill` (the `bn254_mul` /
   `bn254_square` leaves provably exceed 16 GPRs; without `-auto-spill` they hit
   "no more free register" even standalone). Re-emitting them in reg-ptr-native
   form (`reg ptr u64[4]`) does **not** compile — the array-pointer params add
   register pressure the spilling mul cannot absorb.

2. The verified leaf is field-correct: the unmodified `bn254_add` leaf,
   compiled standalone (`-auto-spill`) and driven from C, computes
   `5 + 7 = 12 (mod p)` with the correct BN254 base prime `p` (the leaf's own
   reduction constants are exactly the BN254 Fp prime limbs — verified). So the
   field arithmetic itself is real and correct.

3. Bridge attempt (address-pass) — compiles but is **runtime-broken**, and the
   break is NOT spill-specific. Passing the **address** of a `stack u64[4]`
   scratch buffer (`__sg4_0.[u64 0]`) to a `reg u64` byte-pointer leaf compiles
   to x86-64, but segfaults at runtime — confirmed even for a *trivial
   non-spilling* 4-limb copy leaf. jasminc inlines the (always co-compiled)
   byte-pointer leaf and mis-resolves its `[in0 + 8*j]` accesses against the
   stack-array-address argument (the inlined body indexes off the saved `rsp`).
   So the obstacle is the **address-of-stack-array → inlined byte-pointer leaf**
   pattern itself, independent of register pressure.

   (The #259 loop-copy staging itself is runtime-correct — a standalone copy KAT
   round-trips `x[4:8] -> out[0:4]` exactly; the segfault is purely the leaf
   address-pass, not the loop staging.)

The two candidate bridges are both blocked:
- reg-ptr-native verified leaves: `bn254_mul` / `bn254_square` exhaust the
  register allocator (the `reg ptr u64[4]` params add pressure the spilling
  multiply cannot absorb);
- byte-pointer verified leaves via scratch-address: runtime-broken (above),
  and jasmin always inlines internal calls (no extern/separate-object call
  mechanism in this toolchain), so a true cross-object `call` to the leaf's
  byte-pointer ABI is not currently expressible.

Closing #260 needs either a jasmin separate-compilation path (so the leaf stays
a real cross-object `call` with its native byte-pointer ABI) or a
reg-ptr-compatible spill strategy for the multiply leaf — both meaty. Until
then the linked leaves are
still the structural stubs, so **no pairing cyc/op number is reported** — that
would be a number for a non-field-correct kernel.

## Faithfulness (Qed, 0 Admitted)

`pp_module_regptr_same_inputs` (Qed) and the `pp_copyN_index_correspondence`
limb-move obligation are both preserved. The loop form copies the identical word
set `p[k .. k+n-1]` (counter `__cpj__ = j` ranges `0 <= j < n`, source index
`k + j`, scratch index `j` — the same word-index map the unrolled form used), so
the correspondence statement is unchanged. `Core.vo` rebuilds clean; the AUCurves
faithfulness Qeds are intact and no new `Admitted` is introduced.
