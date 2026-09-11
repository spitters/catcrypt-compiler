/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Number.MontgomeryReduction

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 1000

/-!
# The six-limb (P-384 / BLS12-381) CIOS Montgomery-reduce closed form

`Cios4LimbProven.montRedc4` is the four-word closed form of the CIOS Montgomery
reduce: the composition of four per-word reductions
`Number.montgomeryReduce N (2^64) nP`, with `montRedc4_correct` proving its
output is `< 2N` and `· 2^256 ≡ T (mod N)` (range + Montgomery residue), via the
prime-parametric `montgomeryReduce_comp` / `montgomeryReduce_correct`.

This file is the **six-word** analogue at radix `R = 2^384` (the P-384 /
secp384r1 base field and the BLS12-381 base field are both 6-limb curves):
`montRedc6` composes six per-word reductions, and `montRedc6_correct` proves the
output is `< 2N` and `· 2^384 ≡ T (mod N)`. The proof is the same word-step
argument as `montRedc4_correct` extended by two words — `montgomeryReduce_comp`
fuses the first two words into a radix-`2^128` reduction, then four
`montgomeryReduce_correct` steps add the remaining words, and the congruences
chain into `· 2^384 ≡ T (mod N)`. No new axiom, reuses the in-tree `Number`
Montgomery laws.

## Closes the carried six-limb residue spec

`EmittedReduceWindow6Discharge.emittedReduceWindow6_proven` carries the reduced
value's residue spec (`hv_range : v < 2N`, `hv_cong : v · 2^384 ≡ product
(mod N)`) as named hypotheses — *precisely because* no in-tree six-fold CIOS
closed form was proved (the four-limb discharge got these for free from
`montRedc4_correct`). `montRedc6_correct` supplies exactly that residue spec for
the canonical reduced value `v = montRedc6 N nP product`, under the per-word
Montgomery pin `(N·nP) % 2^64 = 2^64−1` and the feed range `product < 2^64·N`.
`EmittedReduceWindow6Discharge.emittedReduceWindow6_proven_montRedc6` feeds
`montRedc6_correct`'s outputs straight into `emittedReduceWindow6_proven`'s
`hv_range` / `hv_cong` slots, so that follow-up theorem carries the residue spec
as a PROVEN consequence rather than a hypothesis.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Cios6LimbProven

open CatCrypt.Crypto.Number

/-- The 6-fold per-word Montgomery reduction: apply the single-word
    `montgomeryReduce N (2^64) nP` six times (the six CIOS `ciosWord` steps),
    a reduction at the full radix `R = 2^384`. -/
def montRedc6 (N nP T : Nat) : Nat :=
  montgomeryReduce N (2 ^ 64) nP
    (montgomeryReduce N (2 ^ 64) nP
      (montgomeryReduce N (2 ^ 64) nP
        (montgomeryReduce N (2 ^ 64) nP
          (montgomeryReduce N (2 ^ 64) nP
            (montgomeryReduce N (2 ^ 64) nP T)))))

/-- **Six word steps = full-radix `R = 2^384` Montgomery reduction.** Chaining six
    per-word reductions (the CIOS loop body, each a
    `montgomeryReduce … 2^64 …`) is a reduction at `R = 2^384`: the result is
    `< 2N` and `· 2^384 ≡ T (mod N)`, i.e. `≡ T · (2^384)⁻¹ (mod N)`. Proved by
    `montgomeryReduce_comp` (fusing words 1+2 into a radix-`2^128` step) then four
    `montgomeryReduce_correct` steps — the six-limb mirror of `montRedc4_correct`.
    Under the per-word Montgomery pin `(N·nP) % 2^64 = 2^64−1` and the feed range
    `T < 2^64·N`. -/
theorem montRedc6_correct (N nP T : Nat) (hN : 0 < N)
    (hnp64 : (N * nP) % 2 ^ 64 = 2 ^ 64 - 1)
    (hT : T < 2 ^ 64 * N) :
    montRedc6 N nP T < 2 * N ∧ (montRedc6 N nP T) * (2 ^ 384) ≡ T [MOD N] := by
  have h2 : (2 : Nat) ≤ 2 ^ 64 := by norm_num
  -- compose words 1+2 → radix 2^128
  obtain ⟨r2_range, r2_cong⟩ :=
    montgomeryReduce_comp N (2 ^ 64) (2 ^ 64) nP nP T hN (by positivity) h2 hnp64 hnp64 hT
  -- words 3..6: each per-word reduction, fed by the previous `< 2N ≤ 2^64·N` result
  have hin3 : montgomeryReduce N (2 ^ 64) nP (montgomeryReduce N (2 ^ 64) nP T)
      < 2 ^ 64 * N := by
    have : (2 : Nat) * N ≤ 2 ^ 64 * N := by gcongr
    omega
  obtain ⟨r3_range, r3_cong⟩ :=
    montgomeryReduce_correct N (2 ^ 64) nP _ hN (by positivity) hnp64 hin3
  have hin4 : montgomeryReduce N (2 ^ 64) nP
      (montgomeryReduce N (2 ^ 64) nP (montgomeryReduce N (2 ^ 64) nP T))
      < 2 ^ 64 * N := by
    have : (2 : Nat) * N ≤ 2 ^ 64 * N := by gcongr
    omega
  obtain ⟨r4_range, r4_cong⟩ :=
    montgomeryReduce_correct N (2 ^ 64) nP _ hN (by positivity) hnp64 hin4
  have hin5 : montgomeryReduce N (2 ^ 64) nP
      (montgomeryReduce N (2 ^ 64) nP
        (montgomeryReduce N (2 ^ 64) nP (montgomeryReduce N (2 ^ 64) nP T)))
      < 2 ^ 64 * N := by
    have : (2 : Nat) * N ≤ 2 ^ 64 * N := by gcongr
    omega
  obtain ⟨r5_range, r5_cong⟩ :=
    montgomeryReduce_correct N (2 ^ 64) nP _ hN (by positivity) hnp64 hin5
  have hin6 : montgomeryReduce N (2 ^ 64) nP
      (montgomeryReduce N (2 ^ 64) nP
        (montgomeryReduce N (2 ^ 64) nP
          (montgomeryReduce N (2 ^ 64) nP (montgomeryReduce N (2 ^ 64) nP T))))
      < 2 ^ 64 * N := by
    have : (2 : Nat) * N ≤ 2 ^ 64 * N := by gcongr
    omega
  obtain ⟨r6_range, r6_cong⟩ :=
    montgomeryReduce_correct N (2 ^ 64) nP _ hN (by positivity) hnp64 hin6
  refine ⟨r6_range, ?_⟩
  -- name the six per-word results
  set w1 := montgomeryReduce N (2 ^ 64) nP T with hw1
  set w2 := montgomeryReduce N (2 ^ 64) nP w1 with hw2
  set w3 := montgomeryReduce N (2 ^ 64) nP w2 with hw3
  set w4 := montgomeryReduce N (2 ^ 64) nP w3 with hw4
  set w5 := montgomeryReduce N (2 ^ 64) nP w4 with hw5
  set w6 := montgomeryReduce N (2 ^ 64) nP w5 with hw6
  -- chain the congruences: w6 · 2^384 ≡ T (mod N)
  have e384 : (2 : Nat) ^ 384
      = 2 ^ 64 * (2 ^ 64 * (2 ^ 64 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64)))) := by ring
  have step6 : w6 * (2 ^ 384)
      ≡ w5 * (2 ^ 64 * (2 ^ 64 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64)))) [MOD N] := by
    rw [e384]
    calc w6 * (2 ^ 64 * (2 ^ 64 * (2 ^ 64 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64)))))
        = (w6 * 2 ^ 64) * (2 ^ 64 * (2 ^ 64 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64)))) := by ring
      _ ≡ w5 * (2 ^ 64 * (2 ^ 64 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64)))) [MOD N] :=
          r6_cong.mul_right _
  have step5 : w5 * (2 ^ 64 * (2 ^ 64 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64))))
      ≡ w4 * (2 ^ 64 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64))) [MOD N] := by
    calc w5 * (2 ^ 64 * (2 ^ 64 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64))))
        = (w5 * 2 ^ 64) * (2 ^ 64 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64))) := by ring
      _ ≡ w4 * (2 ^ 64 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64))) [MOD N] := r5_cong.mul_right _
  have step4 : w4 * (2 ^ 64 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64)))
      ≡ w3 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64)) [MOD N] := by
    calc w4 * (2 ^ 64 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64)))
        = (w4 * 2 ^ 64) * (2 ^ 64 * (2 ^ 64 * 2 ^ 64)) := by ring
      _ ≡ w3 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64)) [MOD N] := r4_cong.mul_right _
  have step3 : w3 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64)) ≡ w2 * (2 ^ 64 * 2 ^ 64) [MOD N] := by
    calc w3 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64))
        = (w3 * 2 ^ 64) * (2 ^ 64 * 2 ^ 64) := by ring
      _ ≡ w2 * (2 ^ 64 * 2 ^ 64) [MOD N] := r3_cong.mul_right _
  -- r2_cong : w2 · (2^64·2^64) ≡ T  (the fused first-two-words reduction)
  have step2 : w2 * (2 ^ 64 * 2 ^ 64) ≡ T [MOD N] := r2_cong
  exact ((((step6.trans step5).trans step4).trans step3).trans step2)

/-! ## Wiring: `montRedc6_correct` supplies the carried six-limb residue spec

`EmittedReduceWindow6Discharge.emittedReduceWindow6_proven` carries `hv_range`
(`v < 2N`) and `hv_cong` (`v · 2^384 ≡ product (mod N)`) as named hypotheses for
an arbitrary reduced value `v`. Taking `v := montRedc6 N nP product`,
`montRedc6_correct` produces *exactly* that pair (under the per-word pin + feed
range). That wiring is `EmittedReduceWindow6Discharge.emittedReduceWindow6_proven_montRedc6`,
which lives in the discharge file (it imports this one), so the emit remainder
shrinks to the named register realiser `ResReducedWindow6` alone. -/

#check @montRedc6
#check @montRedc6_correct

end CatCrypt.Crypto.SecureCompilation.X86Backend.Cios6LimbProven
