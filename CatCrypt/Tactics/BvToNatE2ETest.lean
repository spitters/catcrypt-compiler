/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Tactics.BvToNat
public import CatCrypt.Crypto.Jasmin.Examples.BignumStep
public import CatCrypt.Crypto.Jasmin.Examples.Curve25519CryptoptPort


@[expose] public section
set_option autoImplicit false

/-!
# E2E test: BignumStep + Layer A on small instruction sequences

Validates that the operational simp set (`BignumStep`) composes with the
`bv_to_nat` decomposition lemmas (Layer A) on tractable cases:

* §1: a single MULX, projected to a Nat polynomial via `mulx_toNat_decomp`.
* §2: MULX followed by ADCX, where the second instruction adds the lo
  half plus a carry-in to a separate register, exercising the carry-chain
  composition that `mulBody_correct` will eventually use at scale.

Each test ends with an `omega`/`linear_combination` close. If these break
when `BignumStep` or `bv_to_nat` change, fix the simp sets — these tests
are the canary for the F1 §3 closure path.
-/

namespace CatCrypt.Tactics.BvToNatE2ETest

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Curve25519CryptoptOps
open CatCrypt.Crypto.Jasmin.Examples.Curve25519CryptoptPort
open CatCrypt.Tactics.BvToNat

/-! ## §1. One-instruction E2E: a single MULX. -/

/-- Running `mulxReg rhi rlo rdx rsrc` on any state `s` produces a state
    whose `rhi`/`rlo` registers hold the (hi, lo) BitVec halves of
    `(s.regs rdx) * (s.regs rsrc)`, and the Nat-level product identity
    `hi · 2^64 + lo = rdx · rsrc` holds. -/
theorem mulx_one_instr_e2e
    (rhi rlo rdx rsrc : String) (hne : rhi ≠ rlo) (s : BignumState) :
    ∃ s', bignumExecPlus [mulxReg rhi rlo rdx rsrc] s = some s' ∧
          (s'.regs rhi).toNat * 2^64 + (s'.regs rlo).toNat
            = (s.regs rdx).toNat * (s.regs rsrc).toNat := by
  -- BignumStep reduces the cons to setReg-of-setReg; the MULX_reg simp
  -- lemma matches mulxReg's exact AST shape.
  refine ⟨_, rfl, ?_⟩
  -- The BignumStep simp set fires automatically (cons, MULX_reg, setReg
  -- chain projections); `vU` unfolds the AST register name; this peels
  -- the goal down to the unfolded `mulx` BitVec.ofNat form.
  simp only [vU, setReg_regs_same, setReg_regs_diff _ _ _ _ hne]
  -- The unfolded form is defeq to `(mulx a b).1.toNat * 2^64 + (mulx a b).2.toNat`,
  -- which is exactly what `mulx_toNat_decomp` proves.
  exact mulx_toNat_decomp (s.regs rdx) (s.regs rsrc)

/-! ## §2. Two-instruction E2E: MULX then ADCX.

Sequence: `(hi, lo) := MULX(rdx, src)` followed by
`(cf', acc') := ADCX(acc, lo, cf)`.

The final state satisfies *two* Nat-level identities, one per
instruction's `_toNat_decomp` lemma:

* MULX:  `hi · 2^64 + lo = rdx · src`
* ADCX:  `cf' · 2^64 + acc' = acc + lo + (cf & 1)`

This validates that the BignumStep simp set composes through a chain
of two instructions, with intermediate state lookups (the second
instruction's `lo` reads the first instruction's output) handled by
`setReg_regs_same`/`setReg_regs_diff`. -/

set_option linter.unusedSimpArgs false in
theorem mulx_adcx_two_instr_e2e
    (rhi rlo rdx rsrc rcf raccum : String)
    (hne_lo_hi    : rlo ≠ rhi)
    (hne_cf_accum : rcf ≠ raccum)
    (hne_cf_hi    : rcf ≠ rhi)
    (hne_cf_lo    : rcf ≠ rlo)
    (hne_accum_hi : raccum ≠ rhi)
    (hne_accum_lo : raccum ≠ rlo)
    (s : BignumState) :
    ∃ s', bignumExecPlus
            [mulxReg rhi rlo rdx rsrc, adcxRR rcf raccum raccum rlo] s
            = some s' ∧
          (s'.regs rhi).toNat * 2^64 + (s'.regs rlo).toNat
            = (s.regs rdx).toNat * (s.regs rsrc).toNat ∧
          (s'.regs rcf).toNat * 2^64 + (s'.regs raccum).toNat
            = (s.regs raccum).toNat + (s'.regs rlo).toNat
              + ((s.regs rcf) &&& 1).toNat := by
  -- Symmetric versions of the disequalities, needed by `setReg_regs_diff`
  -- in both directions.
  have hne_hi_lo    := hne_lo_hi.symm
  have hne_accum_cf := hne_cf_accum.symm
  have hne_hi_cf    := hne_cf_hi.symm
  have hne_lo_cf    := hne_cf_lo.symm
  have hne_hi_accum := hne_accum_hi.symm
  have hne_lo_accum := hne_accum_lo.symm
  refine ⟨_, rfl, ?_, ?_⟩
  · -- MULX identity: same proof shape as §1. The chain is read in both
    -- directions, so we pass all six (a, b)/(b, a) variants.
    simp only [vU, setReg_regs_same,
               setReg_regs_diff _ _ _ _ hne_lo_hi,
               setReg_regs_diff _ _ _ _ hne_hi_lo,
               setReg_regs_diff _ _ _ _ hne_cf_hi,
               setReg_regs_diff _ _ _ _ hne_hi_cf,
               setReg_regs_diff _ _ _ _ hne_accum_hi,
               setReg_regs_diff _ _ _ _ hne_hi_accum,
               setReg_regs_diff _ _ _ _ hne_cf_lo,
               setReg_regs_diff _ _ _ _ hne_lo_cf,
               setReg_regs_diff _ _ _ _ hne_accum_lo,
               setReg_regs_diff _ _ _ _ hne_lo_accum]
    exact mulx_toNat_decomp (s.regs rdx) (s.regs rsrc)
  · -- ADCX identity: raccum and rcf are unchanged by MULX (different regs);
    -- rlo is the post-MULX value.
    simp only [vU, setReg_regs_same,
               setReg_regs_diff _ _ _ _ hne_cf_accum,
               setReg_regs_diff _ _ _ _ hne_accum_cf,
               setReg_regs_diff _ _ _ _ hne_cf_hi,
               setReg_regs_diff _ _ _ _ hne_hi_cf,
               setReg_regs_diff _ _ _ _ hne_cf_lo,
               setReg_regs_diff _ _ _ _ hne_lo_cf,
               setReg_regs_diff _ _ _ _ hne_accum_hi,
               setReg_regs_diff _ _ _ _ hne_hi_accum,
               setReg_regs_diff _ _ _ _ hne_accum_lo,
               setReg_regs_diff _ _ _ _ hne_lo_accum]
    -- Goal is the addCarryIn identity at the Nat level.
    exact addCarryIn_toNat_decomp _ _ _

/-! ## §3. Operational scaling test: 10-instruction MULX/ADCX cascade.

Tests whether the BignumStep `@[simp]` set reduces a 10-instruction
sequence to a closed `some (setReg-chain)` form within a reasonable
time budget. No Nat-level identity is proved here — this is purely a
canary for the operational reduction (the bottleneck for scaling to
the 165-instruction `mulBody`).

If this test ever times out or blows up the elaborator, that's the
signal to pivot to a custom tactic for the chain walk before
attempting `mulBody_correct`. -/

theorem ten_instr_reduces (s : BignumState) :
    ∃ s', bignumExecPlus
            [ mulxReg "rhi1" "rlo1" "rdx" "rsrc1"
            , mulxReg "rhi2" "rlo2" "rdx" "rsrc2"
            , adcxRR  "cf"   "rlo2" "rlo2" "rhi1"
            , adcxRR  "cf"   "rhi2" "rhi2" "z"
            , mulxReg "rhi3" "rlo3" "rdx" "rsrc3"
            , adcxRR  "cf"   "rlo3" "rlo3" "rhi2"
            , adcxRR  "cf"   "rhi3" "rhi3" "z"
            , mulxReg "rhi4" "rlo4" "rdx" "rsrc4"
            , adcxRR  "cf"   "rlo4" "rlo4" "rhi3"
            , adcxRR  "cf"   "rhi4" "rhi4" "z"
            ] s = some s' := by
  exact ⟨_, rfl⟩

/-! ### Scaling finding (recorded for the F1 §3 closure design)

A 5-instruction pure-register prefix reduces and `rfl`-closes within
seconds. Pushing the same pattern to 20 instructions triggers a kernel
deterministic-timeout: `simp` produces the reduced bind-chain quickly,
but the kernel cannot verify the resulting `⟨_, rfl⟩` witness within
the default budget (13+ min observed).

Implication for `mulBody_correct` (165 instructions): the
`∃ s', exec = some s'` framing will not close via `rfl` at scale.
The path forward is to *not* state intermediate state-existence;
instead, prove the final-limb projections directly, where the goal
shape `(loadLimbs s₁ out).get k = (carryMulSpec a b) k` reduces to a
small BitVec arithmetic identity per limb.
-/

def mulBodyPrefix5Pure : List InstrR :=
  [ imulImmReg "rax" "b3" 0x13
  , movReg "rdx" "rax"
  , mulxReg "rcx" "r11" "rdx" "a3"
  , movReg "r8" "rdx"
  , movReg "rdx" "a0"
  ]

theorem mulBodyPrefix5Pure_reduces (s : BignumState) :
    ∃ s', bignumExecPlus mulBodyPrefix5Pure s = some s' := by
  simp [mulBodyPrefix5Pure, mulxReg, movReg, imulImmReg, vU, pv,
        flagPre, flagPost, lvR, lvNone, List.replicate]
  exact ⟨_, rfl⟩

/-! ### Per-register projection attempt — also hits the kernel cliff.

The natural workaround for the rfl-witness scaling issue is to *project*
the resulting state to a single register, hoping the kernel only has to
verify that one register's value, not the whole 20-setReg chain. We
tried:

```
theorem proj_rdi (s : BignumState) :
    ((bignumExecPlus body20 s).map (·.regs "rdi"))
      = some (specific_BitVec_expr s) := by
  simp [...]
```

Result: same kernel deterministic-timeout (~9.5 min), even though only
one register's value is projected. The simp tactic produces a proof
term that *internally* references the whole reduced chain, regardless
of the goal's surface shape — so the kernel still has to verify the
full chain's reduction.

**Implication:** closing `mulBody_correct` purely via the
operational-reduction strategy is blocked by Lean's kernel performance
on terms of this size, not by the proof structure. Workarounds:

1. **Reflection** — define `mulBody_pure : (Fin 5 → BitVec 64) → … →
   Option (Fin 5 → BitVec 64)` as a Lean-level function, prove
   `runMul = mulBody_pure` by `rfl` (small per-instruction reductions
   composed at the Lean level, not the kernel level), then prove
   `mulBody_pure = carryMulSpec` algebraically. This is the
   fiat-crypto-style approach.

2. **Chunked composition** — prove 5-instruction sub-chains via the
   tractable approach, glue them together. Requires manual chunk
   bookkeeping but each chunk is below the kernel cliff.

3. **Custom kernel-friendly tactic** — bespoke tactic that produces
   a smaller proof term via casting. Requires meta-programming.

This iteration of the loop has exhausted the "operational reduction"
attack vector. The path forward is research-grade — closing the loop
and recording the finding for follow-up. -/

end CatCrypt.Tactics.BvToNatE2ETest
