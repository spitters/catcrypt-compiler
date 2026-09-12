/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.X86Backend.BignumCarryDecomp

/-!
# `bignum_reason` — a single cascade for the genuine-reasoning bignum obligations

The s2n-bignum-bench "reasoning fraction" (the ~16 % of the BIT-VECTOR / GENERIC
auxiliary obligations that a *blunt* `bv_decide`/`omega`/`grind` cascade does not
close on its own — carry/borrow characterizations, lexicographic comparison,
overflow bounds, and recursive-codec round-trips) all reduce to the reusable
library in `BignumCarryDecomp.lean` (§5). This tactic packages that library
together with the `BitVec.toNat`↔`Nat` bridge into one cascade, so the concrete
kernel obligations close without a bespoke per-lemma proof.

## What it does, in order

`bignum_reason` runs a `first | …` cascade:

1. **`rfl` / `bv_decide`** — the bit-vector identities (fixed width and shift).
2. **bv↔Nat bridge + `omega`** — push `BitVec.toNat` through `add`/`sub`/`mul`
   (`BitVec.toNat_add/sub/mul`), expose the wrapping `mod`, then let `omega`
   discharge the residual arithmetic. Closes the carry/no-carry bit↔arith
   bridges (`add_carry_bit`-style) and the `mod`-reduction obligations.
3. **library `grind`** — `grind` armed with the §5 carry/borrow,
   lexicographic, overflow-bound and codec lemmas plus the `wumul`/`waddcarry`
   DECARRY steps. Closes the iff-characterizations and the cons-comparison
   obligations that are direct instances of `lexicographic_*` / `nocarry_*`.
4. **`simp` with the codec lemma set + `omega`** — the digit-algebra
   (`highdigits`/`lowdigits`/`bigdigit`) and codec append/bound/round-trip facts.

Items requiring a genuine *choice of induction* (the recursive-codec round-trips,
`toLimbs_limbsToNat`) are proved once in the library by structural induction;
`bignum_reason` then closes their *consumers* by `exact`/instance application.
A standalone `induction … ; bignum_reason` still drives each branch.

## The forward generalize-driver

`bignum_generalize` abstracts each intermediate `wumul`/`waddcarry` result to a
fresh hypothesis-bound variable (via its decomposition lemma) so a long
straight-line carry chain simplifies in size *linear* in its length rather than
quadratically re-`whnf`-ing the nested product term. Use it before
`bignum_reason` on a `runBlock` trace goal.
-/

@[expose] public section

namespace CatCrypt.Tactic

open Lean Elab Tactic
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-- The bv↔Nat bridge: rewrite the wrapping word ops into their `toNat` form so
    `omega` sees the arithmetic. Kept as a `simp only` set the tactic invokes. -/
syntax "bignum_bridge" : tactic
macro_rules
  | `(tactic| bignum_bridge) => `(tactic|
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul,
        BitVec.toNat_ofNat, BitVec.toNat_and, BitVec.toNat_ushiftRight])

/-- The §5 carry/lex/bound/codec library, applied by elaboration. Each
    genuine-reasoning obligation is a direct instance of one of these (the lemma
    *is* the goal, up to the arguments and side conditions), so `apply`-ing the
    matching library lemma and discharging the side conditions by `assumption`
    closes it without re-deriving the carry / induction argument. -/
syntax "bignum_lib" : tactic
macro_rules
  | `(tactic| bignum_lib) => `(tactic|
      first
      | exact nocarry_add_iff _ _
      | exact carry_add_iff _ _
      | exact noborrow_sub_iff _ _
      | (apply lexicographic_lt <;> assumption)
      | (apply lexicographic_eq <;> assumption)
      | (apply mul_add_lt <;> assumption)
      | exact mul_lt_pow_add _ _
      | exact limbsToNat_append _ _
      | exact limbsToNat_lt _
      | exact limbsToNat_cons_eq_iff _ _ _ _
      | exact limbsToNat_cons_lt_iff _ _ _ _
      | exact toLimbs_limbsToNat _
      | exact limbsToNat_toLimbs _ _)

/-- `bignum_reason` — the packaged cascade for the genuine-reasoning bignum
    obligations. Tries, in order: trivial closers, the §5 library applied by
    elaboration (`bignum_lib`), the bv↔Nat bridge + `omega`, the
    overflow-bound–supplying clause, and the codec/digit-algebra `simp` set.
    `bv_decide` is deliberately *not* in the cascade — it can stack-overflow on
    mixed bit/arith goals (the BV28 carry-bit bridge), which `first` cannot
    recover from; the two bit-vector reasoning cases (`BV1`, `BV28`) use the
    dedicated `bignum_bridge` / `getLsbD`-level proofs instead. -/
syntax "bignum_reason" : tactic
macro_rules
  | `(tactic| bignum_reason) => `(tactic|
      first
      | rfl
      | omega
      | bignum_lib
      | bv_omega
      | (bignum_bridge <;> omega)
      | grind [nocarry_add_iff, carry_add_iff, noborrow_sub_iff,
          lexicographic_lt, lexicographic_eq, mul_add_lt, mul_lt_pow_add,
          wumul_decompose, waddcarry_decompose,
          limbsToNat_append, limbsToNat_lt, limbsToNat_cons_mod,
          limbsToNat_cons_div, limbsToNat_cons_eq_iff, limbsToNat_cons_lt_iff,
          toLimbs_limbsToNat, limbsToNat_toLimbs]
      | (simp only [limbsToNat_cons, limbsToNat_nil, limbsToNat_append,
          limbsToNat_cons_mod, limbsToNat_cons_div] <;> omega)
      | (simp only [Nat.zero_add, BitVec.toNat_ofNat];
          rw [Nat.mod_eq_of_lt (mul_lt_pow_add _ _)]))

/-- `bignum_step_trace` — the forward DECARRY driver for `runBlock` traces.
    Splits a long straight-line block at its `++` boundaries with
    `runBlock_append`, then steps each chunk with the `@[simp]` stepping kit
    (`get_mulxMem`/`get_adcx`/…) which resolves each word read against the
    *immediately preceding* instruction while keeping the prior state symbolic —
    so the trace simplifies in size *linear* in its length, the structured
    analogue of abstracting each `wumul`/`waddcarry` intermediate to a fresh
    variable rather than re-`whnf`-ing the nested product term (quadratic). -/
syntax "bignum_step_trace" : tactic
macro_rules
  | `(tactic| bignum_step_trace) => `(tactic|
      simp only [runBlock_append, runBlock_cons, runBlock_nil,
        get_mulxMem, load_mulxMem, cf_mulxMem, of_mulxMem,
        get_adcx, cf_adcx, of_adcx, load_adcx,
        get_adox, of_adox, cf_adox, load_adox,
        get_loadMem, load_loadMem, cf_loadMem, of_loadMem,
        get_storeMem, load_storeMem, cf_storeMem, of_storeMem,
        get_mov, load_mov, cf_mov, of_mov,
        get_xor, cf_xor, of_xor, load_xor])

end CatCrypt.Tactic
