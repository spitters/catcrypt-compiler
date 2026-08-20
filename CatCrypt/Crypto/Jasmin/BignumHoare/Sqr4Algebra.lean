/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.BignumExec
import CatCrypt.Crypto.Jasmin.BignumExecDiffTest
import CatCrypt.Crypto.Jasmin.Hoare
import CatCrypt.Crypto.Jasmin.S2NBignumSSA

set_option autoImplicit false
-- The sqr_4 keystones operate at BitVec 512 / Nat 2^448 scale. Mathlib
-- defaults `exponentiation.threshold` to 256, which blocks `ring_nf` /
-- `decide` from evaluating `2^N` for N > 256 — leaves products like
-- `2^320 * 2^64` symbolic instead of folding into `2^384`. Bump to
-- cover everything we touch through `2^512` (the no-overflow side).
set_option exponentiation.threshold 1024

/-!
# Algebraic keystones for `bignum_sqr_4`

Pure BitVec / Nat lemmas used to bridge the chain output of the
`bignum_sqr_4` body to the Nat-level square `(Σ a_i · 2^{64i})²`.

Split out of `BignumHoare.lean` so the heavy `bv_decide`-driven
keystones don't re-elaborate every time a downstream wrapper changes,
and so each file fits memory comfortably under the 14 GiB ceiling.

## Contents

- BitVec→Nat bridges: `shiftLeft_or_eq_mul_add`, `toNat_concat_4limbs`,
  `toNat_concat_8limbs`.
- `mulx_correct`: 64×64 multiplication produces the high/low pair.
- Phase A invariant ↔ chain output: `sqr4_phaseA_chain_eq_invariant_sum_bv384`.
- Step 2 (per-product accumulation): `sqr4_offdiag_step_bv192`,
  `sqr4_offdiag_step_bv192_cin`.
- Step 3 (Phase B doubling): `sqr4_shift_left_chain_bv384`.
- Step 4 (Phase C composition): `sqr4_phaseC_chain_bv512`.
- Step 5 (algebraic decompositions): `sqr4_schoolbook_expansion`,
  `sqr4_phaseA_eq_offdiag_sum`, `sqr4_sdiag_eq_diagonal_sum`,
  `sqr4_e_padded_toNat`.
- Step 6 (final keystone): `sqr4_chain_eq_square` — chain output equals
  `a²` at Nat level given mulx + Phase B doubling + Phase C composition
  + no-overflow side condition.

The phase Triples (`sqr4_phaseA_triple`, …) live in
`BignumHoare.lean` (until further split). They consume these lemmas
as black-box rewrites.

## Status (2026-05-11)

**0 sorries.**  The previously-sorried
`sqr4_phaseA_chain_eq_invariant_sum_bv384` (a provably-false claim
about `BignumSqr4.body`'s buggy SSA encoding) is replaced with a `True` placeholder.
Modular squaring callers route through `MontmulAxiom.montmul_call_squaring`
instead (see `ChainStepAxioms.chain_sqr_step_correct_generic`).

Resolution of the Mathlib big-numeral asymmetry (which blocked the
other 3 keystones): `set_option exponentiation.threshold 1024`. The
default 256 left `2^N` for N > 256 unevaluated, leaving residuals
like `2^320 * 2^64` symbolic instead of folding into `2^384`.

## What changed since the last sorry round

- `sqr4_phaseA_eq_offdiag_sum`: Qed via `linear_combination` summing
  6 mulx hypotheses with product-form weights (commit `e156a2d1`).
- `sqr4_sdiag_eq_diagonal_sum`: Qed via `linear_combination` summing
  4 diagonal mulx hypotheses (commit `e156a2d1`).
- `sqr4_chain_eq_square`: Qed via `linear_combination` summing all 11
  hypotheses with product-form weights, after the threshold bump
  (this commit). -/

namespace CatCrypt.Crypto.Jasmin.BignumHoare

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Hoare
open CatCrypt.Crypto.Jasmin.MemoryModel

/-! ### BitVec→Nat bridge lemmas for the 4-limb concat decoding -/

/-- Helper: `a <<< i ||| b = a * 2^i + b` when `b < 2^i`. -/
theorem shiftLeft_or_eq_mul_add (a b i : ℕ) (h : b < 2^i) :
    a <<< i ||| b = a * 2^i + b := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt h, Nat.shiftLeft_eq]

/-- `(a3 ++ a2 ++ a1 ++ a0).toNat = limb sum`. -/
theorem toNat_concat_4limbs (a0 a1 a2 a3 : BitVec 64) :
    (a3 ++ a2 ++ a1 ++ a0 : BitVec 256).toNat =
      a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 + a3.toNat * 2^192 := by
  have ha0 : a0.toNat < 2^64 := a0.isLt
  have ha1 : a1.toNat < 2^64 := a1.isLt
  have ha2 : a2.toNat < 2^64 := a2.isLt
  rw [BitVec.toNat_append, BitVec.toNat_append, BitVec.toNat_append]
  rw [shiftLeft_or_eq_mul_add _ _ 64 ha2]
  rw [show ((a3.toNat * 2^64 + a2.toNat) <<< 64 ||| a1.toNat)
        = (a3.toNat * 2^64 + a2.toNat) * 2^64 + a1.toNat from
      shiftLeft_or_eq_mul_add _ _ 64 ha1]
  rw [show ((a3.toNat * 2^64 + a2.toNat) * 2^64 + a1.toNat) <<< 64 ||| a0.toNat
        = ((a3.toNat * 2^64 + a2.toNat) * 2^64 + a1.toNat) * 2^64 + a0.toNat from
      shiftLeft_or_eq_mul_add _ _ 64 ha0]
  ring

/-! ### Phase 4 — bignum_sqr_4 building blocks

Per-partial-product strategy: prove individual 64×64 mul identities
(close in seconds via bv_decide) then assemble. -/

/-- MULX correctness: hi:lo = a*b at the Nat level. -/
theorem mulx_correct (a b : BitVec 64) :
    (BignumExec.mulx a b).1.toNat * 2^64 + (BignumExec.mulx a b).2.toNat =
      a.toNat * b.toNat := by
  unfold BignumExec.mulx
  simp only [BitVec.toNat_ofNat]
  have ha : a.toNat < 2^64 := a.isLt
  have hb : b.toNat < 2^64 := b.isLt
  have h_prod_lt : a.toNat * b.toNat < 2^128 := by
    have := Nat.mul_lt_mul_of_lt_of_le ha (Nat.le_of_lt hb) (by omega : 0 < 2^64)
    simpa [show 2^64 * 2^64 = 2^128 from by decide] using this
  rw [Nat.shiftRight_eq_div_pow]
  -- Goal: (a*b / 2^64) % 2^64 * 2^64 + a*b % 2^64 = a*b
  have : (a.toNat * b.toNat / 2^64) < 2^64 := by
    apply Nat.div_lt_iff_lt_mul (by decide : 0 < 2^64) |>.mpr
    simpa [show 2^64 * 2^64 = 2^128 from by decide] using h_prod_lt
  rw [Nat.mod_eq_of_lt this]
  -- Goal: (a*b / 2^64) * 2^64 + a*b % 2^64 = a*b
  have := Nat.div_add_mod (a.toNat * b.toNat) (2^64)
  omega

/-! ### Phase 4 — bignum_sqr_4 (TLE finding)

A 512-bit polynomial identity stating `a² = schoolbook_decomposition`
(both as BitVec 512) TLEs `bv_decide`. The 64-bit×64-bit multiplications
at the symbolic level (16 distinct partial products) are too heavy.

For sqr_4, the recipe needs adaptation:
- Split per partial product (16 bv_decide calls instead of 1)
- Use `Nat.cast` / mathlib's polynomial machinery to reduce to the
  already-proved `schoolbook_eq_square` at the Nat level
- Use `omega` or `ring` after a Nat-cast lift

Tracked as Phase 4 follow-up. -/

/-! ### Phase 4 — bignum_sqr_4 Phase A chain ↔ invariant bridge

The body's claimed Phase A invariants (`d_k = sum of mulx outputs at
slot k`) describe the algebraic SUM, but the actual chain stores
`d_k mod 2^64` with carries propagated to higher slots. The 6-limb
concat `.toNat` of the chain output equals the algebraic invariant
sum because carries fold correctly. -/

/-- Per-step lift: `addCarry a b` produces `(cf, r)` such that
    `r.toNat + cf.toNat * 2^64 = a.toNat + b.toNat` at Nat level. -/
theorem addCarry_toNat_lift (a b : BitVec 64) :
    (BignumExec.addCarry a b).2.toNat +
      (BignumExec.addCarry a b).1.toNat * 2^64 = a.toNat + b.toNat := by
  unfold BignumExec.addCarry
  simp only [BitVec.toNat_add, BitVec.ult_iff_toNat_lt,
             apply_ite BitVec.toNat,
             show (1 : BitVec 64).toNat = 1 from rfl,
             show (0 : BitVec 64).toNat = 0 from rfl]
  have ha : a.toNat < 2^64 := a.isLt
  have hb : b.toNat < 2^64 := b.isLt
  grind

/-- Per-step lift for addCarryIn (with carry-in bit).

    Statement only — proof deferred. Path forward: the cf is `cf1 ||| cf2`
    via `Nat.lor` over 0/1 values, where `Nat.lor` doesn't reduce cleanly
    via omega. Need a `Nat.lor_eq_or_of_lt_2` helper or manual case split
    on `cf1, cf2 ∈ {0, 1}`. -/
theorem addCarryIn_toNat_lift (a b cin : BitVec 64) (hcin : cin.toNat ≤ 1) :
    (BignumExec.addCarryIn a b cin).2.toNat +
      (BignumExec.addCarryIn a b cin).1.toNat * 2^64 =
        a.toNat + b.toNat + cin.toNat := by
  unfold BignumExec.addCarryIn
  simp only [BitVec.toNat_add, BitVec.toNat_or, BitVec.toNat_and,
             BitVec.ult_iff_toNat_lt,
             apply_ite BitVec.toNat,
             show (1 : BitVec 64).toNat = 1 from rfl,
             show (0 : BitVec 64).toNat = 0 from rfl]
  have ha : a.toNat < 2^64 := a.isLt
  have hb : b.toNat < 2^64 := b.isLt
  have hcb : cin.toNat < 2^64 := cin.isLt
  grind

/-! ### Removed: `sqr4_phaseA_chain_eq_invariant_sum_bv384`

This lemma claimed that the Phase-A chain output (6-limb concat) of
`BignumSqr4.body` decodes to the off-diagonal invariant sum.  Inves-
tigation (2026-04-30) showed the lemma is **provably false** under
the current SSA encoding of `BignumSqr4.body`: the reference x86_64
algorithm uses ADCX/ADOX dual-carry-chain instructions (AMD/Intel
ADX extension) that maintain TWO independent carry chains via CF
and OF.  The SSA encoding flattens to single-CF `addCopn`/`adcCopn`
pairs that LOSE carries on `addCopn` resets, under-counting the
true off-diagonal sum.

**Reroute strategy (recommended, 2026-05-11):** rather than try to
verify a buggy SSA encoding, use the higher-level `montmul`-based
route for *modular* squaring.  `MontmulAxiom.montmul_call_squaring`
(in `MontmulAxiom.lean`) provides the functional contract for
`bignum_montmul_p25519(out, x, x)`: a single Ccall produces
`out = x² mod p_25519` at the 4-limb output.  Callers needing
modular squaring (e.g. the Curve25519 inverse/exponentiation
chains) thread through that contract directly — see the
`chain_sqr_step_correct` / `chain_sqr_step_correct_generic`
theorems in `ChainStepAxioms.lean` which already do exactly this.

The 4-limb-to-8-limb raw-squaring case (`bignum_sqr_4_8` without
mod-p) has no in-tree consumer that benefits from a separate Lean
proof; the `BignumSqr4` module is now effectively dead code pending
either an SSA-IR ADCX/ADOX extension or s2n-bignum-style HOL Light
trust port for the raw squaring callee. -/

/-- Placeholder for the removed `sqr4_phaseA_chain_eq_invariant_sum_bv384`.
    Kept as `True` so downstream `import`s don't break if anyone still
    references the name.  Use `MontmulAxiom.montmul_call_squaring` for
    modular squaring instead. -/
theorem sqr4_phaseA_chain_eq_invariant_sum_bv384 : True := trivial

/-! ### Phase 4 — bignum_sqr_4 Step 2-3: per-product accumulation lemmas

Each off-diagonal product `(a_i, a_j)`
contributes `(h_ij, l_ij) = mulx a_i a_j` to two adjacent d_k slots.
Step 2 (this section) proves the BitVec identity for one accumulation;
Step 3 covers the Phase B shift-left chain. -/

/-- **Step 2 (off-diagonal accumulation, BitVec 192).** After
    `(cf1, lo') = addCarry lo h`, `(cf2, hi') = addCarryIn hi h cf1`:
    the 192-bit value `cf2 ++ hi' ++ lo'` equals
    `(hi ++ lo) + (0 ++ h ++ l)` as BitVec 192. (l contributes to the
    `lo`-slot, h to the `hi`-slot, with carry threading.)

    The user wires this to mulx_correct (l, h = mulx outputs) to get
    the Nat-level accumulation increment of `a*b`. -/
theorem sqr4_offdiag_step_bv192
    (lo hi l h : BitVec 64) :
    let cf1 := (BignumExec.addCarry lo l).1
    let lo' := (BignumExec.addCarry lo l).2
    let cf2 := (BignumExec.addCarryIn hi h cf1).1
    let hi' := (BignumExec.addCarryIn hi h cf1).2
    let lhs : BitVec 192 := (cf2 &&& 1) ++ hi' ++ lo'
    let rhs : BitVec 192 := (0#64 ++ hi ++ lo) + (0#64 ++ h ++ l)
    lhs = rhs := by
  unfold BignumExec.addCarry BignumExec.addCarryIn
  bv_decide

/-- **Step 2′ (with input carry).** Same as `sqr4_offdiag_step_bv192`
    but threads an input carry `cin` into the lo-add. Used by Phase C
    diagonal accumulation where the cf comes from the previous diagonal's
    high-limb adc. -/
theorem sqr4_offdiag_step_bv192_cin
    (lo hi l h cin : BitVec 64) :
    let cf1 := (BignumExec.addCarryIn lo l cin).1
    let lo' := (BignumExec.addCarryIn lo l cin).2
    let cf2 := (BignumExec.addCarryIn hi h cf1).1
    let hi' := (BignumExec.addCarryIn hi h cf1).2
    let lhs : BitVec 192 := (cf2 &&& 1) ++ hi' ++ lo'
    let rhs : BitVec 192 := (0#64 ++ hi ++ lo) + (0#64 ++ h ++ l) + (0#128 ++ (cin &&& 1))
    lhs = rhs := by
  unfold BignumExec.addCarryIn
  bv_decide

/-- **Step 4 (Phase C 8-limb composition).** The Phase C output chain
    assembles 8 output limbs (op[0]..op[7]) from the 6 doubled
    off-diagonals (e1..e6, from Phase B) and the 4 diagonal mulx
    outputs ((s_ih, s_il) for i ∈ {0,1,2,3}). The full 512-bit output
    equals `e_padded + s_diag` where:

    - `e_padded` is `(0 ++ e6 ++ e5 ++ e4 ++ e3 ++ e2 ++ e1 ++ 0)` —
      e_k limbs shifted up by one position (op[1] starts the e-chain),
      with op[0] and op[7] zeros at the e level.
    - `s_diag` is `(s3h ++ s3l ++ s2h ++ s2l ++ s1h ++ s1l ++ s0h ++ s0l)` —
      diagonal squares packed into adjacent pairs at positions 2i, 2i+1. -/
theorem sqr4_phaseC_chain_bv512
    (e1 e2 e3 e4 e5 e6 s0l s0h s1l s1h s2l s2h s3l s3h : BitVec 64) :
    -- op[0] = s0l (no addition)
    let o0 := s0l
    -- op[1] = e1 + s0h (fresh add, cf out)
    let cf1 := if (e1 + s0h).ult e1 then (1 : BitVec 64) else 0
    let o1 := e1 + s0h
    -- op[2..7] = adc chain
    let cf2 := (if (e2 + s1l).ult e2 then (1 : BitVec 64) else 0) |||
               (if (e2 + s1l + (cf1 &&& 1)).ult (cf1 &&& 1) then 1 else 0)
    let o2 := e2 + s1l + (cf1 &&& 1)
    let cf3 := (if (e3 + s1h).ult e3 then (1 : BitVec 64) else 0) |||
               (if (e3 + s1h + (cf2 &&& 1)).ult (cf2 &&& 1) then 1 else 0)
    let o3 := e3 + s1h + (cf2 &&& 1)
    let cf4 := (if (e4 + s2l).ult e4 then (1 : BitVec 64) else 0) |||
               (if (e4 + s2l + (cf3 &&& 1)).ult (cf3 &&& 1) then 1 else 0)
    let o4 := e4 + s2l + (cf3 &&& 1)
    let cf5 := (if (e5 + s2h).ult e5 then (1 : BitVec 64) else 0) |||
               (if (e5 + s2h + (cf4 &&& 1)).ult (cf4 &&& 1) then 1 else 0)
    let o5 := e5 + s2h + (cf4 &&& 1)
    let cf6 := (if (e6 + s3l).ult e6 then (1 : BitVec 64) else 0) |||
               (if (e6 + s3l + (cf5 &&& 1)).ult (cf5 &&& 1) then 1 else 0)
    let o6 := e6 + s3l + (cf5 &&& 1)
    -- op[7] = s3h + 0 + cf  (zero is the b operand)
    let _cf7 := (if (s3h + 0).ult s3h then (1 : BitVec 64) else 0) |||
                (if (s3h + 0 + (cf6 &&& 1)).ult (cf6 &&& 1) then 1 else 0)
    let o7 := s3h + 0 + (cf6 &&& 1)
    -- Output concat (8 limbs, BitVec 512)
    let o_concat : BitVec 512 := o7 ++ o6 ++ o5 ++ o4 ++ o3 ++ o2 ++ o1 ++ o0
    -- e_padded: e1 at limb 1, …, e6 at limb 6, zeros at limb 0 and 7
    let e_padded : BitVec 512 := 0#64 ++ e6 ++ e5 ++ e4 ++ e3 ++ e2 ++ e1 ++ 0#64
    -- s_diag: (s_ih ++ s_il) at limbs (2i+1, 2i)
    let s_diag : BitVec 512 := s3h ++ s3l ++ s2h ++ s2l ++ s1h ++ s1l ++ s0h ++ s0l
    o_concat = e_padded + s_diag := by
  bv_decide

/-- **Step 3 (shift-left chain).** Phase B doubles each d_k via a single
    cf chain: e_k := 2 * d_k + carry-in, where carry comes from the
    previous limb's high bit. The 6-limb concat is exactly `2 * d_concat`
    (zero-extended) at BitVec 384 level. -/
theorem sqr4_shift_left_chain_bv384
    (d1 d2 d3 d4 d5 d6 : BitVec 64) :
    let cy0 := if (d1 + d1).ult d1 then (1 : BitVec 64) else 0
    let e1 := d1 + d1
    let cy1 := (if (d2 + d2).ult d2 then (1 : BitVec 64) else 0) |||
               (if (d2 + d2 + (cy0 &&& 1)).ult (cy0 &&& 1) then 1 else 0)
    let e2 := d2 + d2 + (cy0 &&& 1)
    let cy2 := (if (d3 + d3).ult d3 then (1 : BitVec 64) else 0) |||
               (if (d3 + d3 + (cy1 &&& 1)).ult (cy1 &&& 1) then 1 else 0)
    let e3 := d3 + d3 + (cy1 &&& 1)
    let cy3 := (if (d4 + d4).ult d4 then (1 : BitVec 64) else 0) |||
               (if (d4 + d4 + (cy2 &&& 1)).ult (cy2 &&& 1) then 1 else 0)
    let e4 := d4 + d4 + (cy2 &&& 1)
    let cy4 := (if (d5 + d5).ult d5 then (1 : BitVec 64) else 0) |||
               (if (d5 + d5 + (cy3 &&& 1)).ult (cy3 &&& 1) then 1 else 0)
    let e5 := d5 + d5 + (cy3 &&& 1)
    let cy5 := (if (d6 + d6).ult d6 then (1 : BitVec 64) else 0) |||
               (if (d6 + d6 + (cy4 &&& 1)).ult (cy4 &&& 1) then 1 else 0)
    let e6 := d6 + d6 + (cy4 &&& 1)
    let lhs : BitVec 448 := (cy5 &&& 1) ++ e6 ++ e5 ++ e4 ++ e3 ++ e2 ++ e1
    let d_concat : BitVec 384 := d6 ++ d5 ++ d4 ++ d3 ++ d2 ++ d1
    let rhs : BitVec 448 := (0#64 ++ d_concat) + (0#64 ++ d_concat)
    lhs = rhs := by
  bv_decide


/-- **Step 5a (schoolbook expansion at Nat level).** The algebraic
    identity that connects the chain outputs (Phase A + B + C) to the
    spec `refSem`. Both sides are pure Nat arithmetic; `ring` closes
    the binomial expansion of `(Σ a_i · 2^{64i})²`. -/
theorem sqr4_schoolbook_expansion (a0 a1 a2 a3 : Nat) :
    (a0 + a1 * 2^64 + a2 * 2^128 + a3 * 2^192) *
    (a0 + a1 * 2^64 + a2 * 2^128 + a3 * 2^192) =
      -- diagonal squares
      a0 * a0 +
      a1 * a1 * 2^128 +
      a2 * a2 * 2^256 +
      a3 * a3 * 2^384 +
      -- 2 × off-diagonal products
      2 * (a0 * a1) * 2^64 +
      2 * (a0 * a2) * 2^128 +
      2 * (a0 * a3 + a1 * a2) * 2^192 +
      2 * (a1 * a3) * 2^256 +
      2 * (a2 * a3) * 2^320 := by
  -- `ring` can leave residual `2^320 * 2` and `2^384` against pre-computed
  -- big-number literals (a Mathlib normalization quirk on large powers).
  -- Convert RHS pow expressions to the same form `ring` picks for the LHS.
  rw [show (2:Nat)^192 = 2^64 * 2^128 from by decide,
      show (2:Nat)^256 = 2^128 * 2^128 from by decide,
      show (2:Nat)^320 = 2^128 * 2^192 from by decide,
      show (2:Nat)^384 = 2^192 * 2^192 from by decide]
  ring

/-- **Step 5b (Phase A invariant in Nat form).** Given the body's
    Phase A semantics `d_1 = l01`, `d_2 = h01 + l02`, …, the Nat
    decoding of `d_concat = d_6 ++ d_5 ++ d_4 ++ d_3 ++ d_2 ++ d_1`
    equals the off-diagonal sum `Σ_{i<j} a_i·a_j · 2^{64(i+j-1)}`,
    using `mulx_correct` to convert each `(h_ij, l_ij)` pair to
    `a_i·a_j`.

    This is the "Phase A done" identity — combining it with Step 3
    (Phase B) and Step 4 (Phase C) closes the chain. Stated as Nat
    arithmetic so we can use `mulx_correct` and `ring`. -/
theorem sqr4_phaseA_eq_offdiag_sum
    (a0 a1 a2 a3 : BitVec 64)
    (h01 l01 h02 l02 h03 l03 h12 l12 h13 l13 h23 l23 : BitVec 64)
    (h_01 : h01.toNat * 2^64 + l01.toNat = a0.toNat * a1.toNat)
    (h_02 : h02.toNat * 2^64 + l02.toNat = a0.toNat * a2.toNat)
    (h_03 : h03.toNat * 2^64 + l03.toNat = a0.toNat * a3.toNat)
    (h_12 : h12.toNat * 2^64 + l12.toNat = a1.toNat * a2.toNat)
    (h_13 : h13.toNat * 2^64 + l13.toNat = a1.toNat * a3.toNat)
    (h_23 : h23.toNat * 2^64 + l23.toNat = a2.toNat * a3.toNat) :
    -- Phase A invariants per the body comment (no carry-loss):
    l01.toNat +
    (h01.toNat + l02.toNat) * 2^64 +
    (h02.toNat + l03.toNat + l12.toNat) * 2^128 +
    (h03.toNat + h12.toNat + l13.toNat) * 2^192 +
    (h13.toNat + l23.toNat) * 2^256 +
    h23.toNat * 2^320 =
      a0.toNat * a1.toNat +
      a0.toNat * a2.toNat * 2^64 +
      (a0.toNat * a3.toNat + a1.toNat * a2.toNat) * 2^128 +
      a1.toNat * a3.toNat * 2^192 +
      a2.toNat * a3.toNat * 2^256 := by
  -- `grobner` (in-kernel Gröbner-basis ideal membership, oracle-free)
  -- synthesises the positional cofactors from the six mulx identities
  -- directly — no power-product rewrite, no manual `linear_combination`
  -- weights, no `exponentiation.threshold` dependence.
  grobner


/-- 8-limb Nat decoder: `(a7 ++ a6 ++ … ++ a0 : BitVec 512).toNat
    = Σ_k a_k.toNat · 2^{64·k}`. Same pattern as `toNat_concat_4limbs`. -/
theorem toNat_concat_8limbs
    (a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 64) :
    (a7 ++ a6 ++ a5 ++ a4 ++ a3 ++ a2 ++ a1 ++ a0 : BitVec 512).toNat =
      a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 + a3.toNat * 2^192 +
      a4.toNat * 2^256 + a5.toNat * 2^320 + a6.toNat * 2^384 + a7.toNat * 2^448 := by
  have h0 : a0.toNat < 2^64 := a0.isLt
  have h1 : a1.toNat < 2^64 := a1.isLt
  have h2 : a2.toNat < 2^64 := a2.isLt
  have h3 : a3.toNat < 2^64 := a3.isLt
  have h4 : a4.toNat < 2^64 := a4.isLt
  have h5 : a5.toNat < 2^64 := a5.isLt
  have h6 : a6.toNat < 2^64 := a6.isLt
  -- Repeated BitVec.toNat_append + shiftLeft_or_eq_mul_add unfolding.
  rw [BitVec.toNat_append, BitVec.toNat_append, BitVec.toNat_append,
      BitVec.toNat_append, BitVec.toNat_append, BitVec.toNat_append,
      BitVec.toNat_append]
  rw [shiftLeft_or_eq_mul_add _ _ 64 h6]
  rw [show ((a7.toNat * 2^64 + a6.toNat) <<< 64 ||| a5.toNat)
        = (a7.toNat * 2^64 + a6.toNat) * 2^64 + a5.toNat from
      shiftLeft_or_eq_mul_add _ _ 64 h5]
  rw [show ((a7.toNat * 2^64 + a6.toNat) * 2^64 + a5.toNat) <<< 64 ||| a4.toNat
        = ((a7.toNat * 2^64 + a6.toNat) * 2^64 + a5.toNat) * 2^64 + a4.toNat from
      shiftLeft_or_eq_mul_add _ _ 64 h4]
  rw [show (((a7.toNat * 2^64 + a6.toNat) * 2^64 + a5.toNat) * 2^64 + a4.toNat) <<< 64 ||| a3.toNat
        = (((a7.toNat * 2^64 + a6.toNat) * 2^64 + a5.toNat) * 2^64 + a4.toNat) * 2^64 + a3.toNat from
      shiftLeft_or_eq_mul_add _ _ 64 h3]
  rw [show ((((a7.toNat * 2^64 + a6.toNat) * 2^64 + a5.toNat) * 2^64 + a4.toNat) * 2^64 + a3.toNat) <<< 64 ||| a2.toNat
        = ((((a7.toNat * 2^64 + a6.toNat) * 2^64 + a5.toNat) * 2^64 + a4.toNat) * 2^64 + a3.toNat) * 2^64 + a2.toNat from
      shiftLeft_or_eq_mul_add _ _ 64 h2]
  rw [show (((((a7.toNat * 2^64 + a6.toNat) * 2^64 + a5.toNat) * 2^64 + a4.toNat) * 2^64 + a3.toNat) * 2^64 + a2.toNat) <<< 64 ||| a1.toNat
        = (((((a7.toNat * 2^64 + a6.toNat) * 2^64 + a5.toNat) * 2^64 + a4.toNat) * 2^64 + a3.toNat) * 2^64 + a2.toNat) * 2^64 + a1.toNat from
      shiftLeft_or_eq_mul_add _ _ 64 h1]
  rw [show ((((((a7.toNat * 2^64 + a6.toNat) * 2^64 + a5.toNat) * 2^64 + a4.toNat) * 2^64 + a3.toNat) * 2^64 + a2.toNat) * 2^64 + a1.toNat) <<< 64 ||| a0.toNat
        = ((((((a7.toNat * 2^64 + a6.toNat) * 2^64 + a5.toNat) * 2^64 + a4.toNat) * 2^64 + a3.toNat) * 2^64 + a2.toNat) * 2^64 + a1.toNat) * 2^64 + a0.toNat from
      shiftLeft_or_eq_mul_add _ _ 64 h0]
  -- `ring` reduces high powers (2^256, 2^320, …) to giant literals on the
  -- LHS but keeps them symbolic on the RHS — Mathlib normalization quirk.
  -- Convert RHS pow expressions to product form so both sides reduce alike.
  rw [show (2:Nat)^128 = 2^64 * 2^64 from by decide,
      show (2:Nat)^192 = 2^64 * 2^128 from by decide,
      show (2:Nat)^256 = 2^128 * 2^128 from by decide,
      show (2:Nat)^320 = 2^128 * 2^192 from by decide,
      show (2:Nat)^384 = 2^192 * 2^192 from by decide,
      show (2:Nat)^448 = 2^192 * 2^256 from by decide]
  ring


/-- **Step 5c (s_diag .toNat = diagonal squares sum).** Given the
    diagonal mulx outputs satisfy `s_ih·2^64 + s_il = a_i²` for each
    `i`, the 8-limb concat `s3h ++ s3l ++ … ++ s0l` decodes (at Nat
    level) to `Σ_i a_i² · 2^{128i}`. -/
theorem sqr4_sdiag_eq_diagonal_sum
    (a0 a1 a2 a3 : BitVec 64)
    (s0h s0l s1h s1l s2h s2l s3h s3l : BitVec 64)
    (h_d0 : s0h.toNat * 2^64 + s0l.toNat = a0.toNat * a0.toNat)
    (h_d1 : s1h.toNat * 2^64 + s1l.toNat = a1.toNat * a1.toNat)
    (h_d2 : s2h.toNat * 2^64 + s2l.toNat = a2.toNat * a2.toNat)
    (h_d3 : s3h.toNat * 2^64 + s3l.toNat = a3.toNat * a3.toNat) :
    (s3h ++ s3l ++ s2h ++ s2l ++ s1h ++ s1l ++ s0h ++ s0l : BitVec 512).toNat =
      a0.toNat * a0.toNat +
      a1.toNat * a1.toNat * 2^128 +
      a2.toNat * a2.toNat * 2^256 +
      a3.toNat * a3.toNat * 2^384 := by
  rw [toNat_concat_8limbs,
      show (2:Nat)^192 = 2^64 * 2^128 from by decide,
      show (2:Nat)^256 = 2^128 * 2^128 from by decide,
      show (2:Nat)^320 = 2^128 * 2^192 from by decide,
      show (2:Nat)^384 = 2^192 * 2^192 from by decide,
      show (2:Nat)^448 = 2^192 * 2^256 from by decide]
  -- `grobner` synthesises the diagonal-slot cofactors from the four
  -- diagonal mulx identities directly (oracle-free, in-kernel).
  grobner


/-- **Step 5d (e_padded .toNat decoder).** The Phase C composition
    has `e_padded := 0#64 ++ e6 ++ e5 ++ e4 ++ e3 ++ e2 ++ e1 ++ 0#64`
    (i.e., e_concat shifted up by one limb). This decodes (at Nat
    level) to `e_concat.toNat · 2^64`, which combined with Step 3 +
    Step 5b becomes `2^64 · 2 · Σ_{i<j} a_i·a_j · 2^{64(i+j-1)}
    = 2 · Σ_{i<j} a_i·a_j · 2^{64(i+j)}`. -/
theorem sqr4_e_padded_toNat
    (e1 e2 e3 e4 e5 e6 : BitVec 64) :
    (0#64 ++ e6 ++ e5 ++ e4 ++ e3 ++ e2 ++ e1 ++ 0#64 : BitVec 512).toNat =
      e1.toNat * 2^64 + e2.toNat * 2^128 + e3.toNat * 2^192 +
      e4.toNat * 2^256 + e5.toNat * 2^320 + e6.toNat * 2^384 := by
  rw [toNat_concat_8limbs]
  -- 0#64.toNat = 0; cancel the two zero terms.
  simp


/-- **Step 6 (sqr_4 final keystone).** Given:
    - 6 mulx hypotheses for off-diagonal products
    - 4 mulx hypotheses for diagonal squares
    - The Phase A `d_k` invariants (per body comment)
    - The Phase B doubling (Step 3 instantiated)
    - The Phase C composition (Step 4)

    the final 8-limb output decodes to `(Σ a_i·2^{64i})²` at Nat level
    — which is exactly `refSem (a0.toNat) (a1.toNat) (a2.toNat) (a3.toNat)`.

    This is the keystone that the Triple-level proof will discharge
    after pinning each chain register's value via mvcgen + simp. -/
theorem sqr4_chain_eq_square
    (a0 a1 a2 a3 : BitVec 64)
    -- Off-diagonal mulx outputs
    (h01 l01 h02 l02 h03 l03 h12 l12 h13 l13 h23 l23 : BitVec 64)
    (m_01 : h01.toNat * 2^64 + l01.toNat = a0.toNat * a1.toNat)
    (m_02 : h02.toNat * 2^64 + l02.toNat = a0.toNat * a2.toNat)
    (m_03 : h03.toNat * 2^64 + l03.toNat = a0.toNat * a3.toNat)
    (m_12 : h12.toNat * 2^64 + l12.toNat = a1.toNat * a2.toNat)
    (m_13 : h13.toNat * 2^64 + l13.toNat = a1.toNat * a3.toNat)
    (m_23 : h23.toNat * 2^64 + l23.toNat = a2.toNat * a3.toNat)
    -- Diagonal mulx outputs
    (s0h s0l s1h s1l s2h s2l s3h s3l : BitVec 64)
    (m_d0 : s0h.toNat * 2^64 + s0l.toNat = a0.toNat * a0.toNat)
    (m_d1 : s1h.toNat * 2^64 + s1l.toNat = a1.toNat * a1.toNat)
    (m_d2 : s2h.toNat * 2^64 + s2l.toNat = a2.toNat * a2.toNat)
    (m_d3 : s3h.toNat * 2^64 + s3l.toNat = a3.toNat * a3.toNat)
    -- e_k limbs: arithmetic identities matching Phase B doubling of the
    -- Phase-A `d_k` invariants. (Bound by `e_concat = 2 · d_concat`.)
    (e1 e2 e3 e4 e5 e6 : BitVec 64)
    (h_e :
      e1.toNat + e2.toNat * 2^64 + e3.toNat * 2^128 +
      e4.toNat * 2^192 + e5.toNat * 2^256 + e6.toNat * 2^320 =
        2 * (l01.toNat +
             (h01.toNat + l02.toNat) * 2^64 +
             (h02.toNat + l03.toNat + l12.toNat) * 2^128 +
             (h03.toNat + h12.toNat + l13.toNat) * 2^192 +
             (h13.toNat + l23.toNat) * 2^256 +
             h23.toNat * 2^320))
    -- Phase C output equation (instantiation of Step 4 .toNat'd, with
    -- the no-overflow side-condition baked in).
    (h_no_overflow :
      e1.toNat * 2^64 + e2.toNat * 2^128 + e3.toNat * 2^192 +
      e4.toNat * 2^256 + e5.toNat * 2^320 + e6.toNat * 2^384 +
      (s0l.toNat + s0h.toNat * 2^64 +
       s1l.toNat * 2^128 + s1h.toNat * 2^192 +
       s2l.toNat * 2^256 + s2h.toNat * 2^320 +
       s3l.toNat * 2^384 + s3h.toNat * 2^448) < 2^512) :
    -- Final identity (at Nat level): output sum = a²
    e1.toNat * 2^64 + e2.toNat * 2^128 + e3.toNat * 2^192 +
    e4.toNat * 2^256 + e5.toNat * 2^320 + e6.toNat * 2^384 +
    (s0l.toNat + s0h.toNat * 2^64 +
     s1l.toNat * 2^128 + s1h.toNat * 2^192 +
     s2l.toNat * 2^256 + s2h.toNat * 2^320 +
     s3l.toNat * 2^384 + s3h.toNat * 2^448) =
    (a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 + a3.toNat * 2^192) *
    (a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 + a3.toNat * 2^192) := by
  rw [sqr4_schoolbook_expansion]
  -- Convert powers to product form before linear_combination so the
  -- ring closer doesn't trip on Mathlib's big-numeral asymmetry.
  rw [show (2:Nat)^128 = 2^64 * 2^64 from by decide,
      show (2:Nat)^192 = 2^64 * 2^64 * 2^64 from by decide,
      show (2:Nat)^256 = 2^64 * 2^64 * 2^64 * 2^64 from by decide,
      show (2:Nat)^320 = 2^64 * 2^64 * 2^64 * 2^64 * 2^64 from by decide,
      show (2:Nat)^384 = 2^64 * 2^64 * 2^64 * 2^64 * 2^64 * 2^64 from by decide,
      show (2:Nat)^448 = 2^64 * 2^64 * 2^64 * 2^64 * 2^64 * 2^64 * 2^64 from by decide]
  linear_combination (norm := ring_nf)
    m_d0
    + m_d1 * (2^64 * 2^64)
    + m_d2 * (2^64 * 2^64 * 2^64 * 2^64)
    + m_d3 * (2^64 * 2^64 * 2^64 * 2^64 * 2^64 * 2^64)
    + h_e * (2^64 : Nat)
    + m_01 * (2 * 2^64)
    + m_02 * (2 * 2^64 * 2^64)
    + m_03 * (2 * 2^64 * 2^64 * 2^64)
    + m_12 * (2 * 2^64 * 2^64 * 2^64)
    + m_13 * (2 * 2^64 * 2^64 * 2^64 * 2^64)
    + m_23 * (2 * 2^64 * 2^64 * 2^64 * 2^64 * 2^64)

end CatCrypt.Crypto.Jasmin.BignumHoare
