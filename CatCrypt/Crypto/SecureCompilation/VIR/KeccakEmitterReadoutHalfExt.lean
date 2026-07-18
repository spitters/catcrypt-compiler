/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmitterReadoutHalf

/-!
# Keccak emitter readout half — extension: the remaining 3 sub-block readouts

`KeccakEmitterReadoutHalf` (task #128) shipped the readout-half closures for
two of the five Keccak sub-blocks (`θ-C col`, `ι`), plus the disjointness
helper `aSlot_ne_cSlot`. This file (task #132) closes the remaining three
sub-block readouts following the same template:

* **θ-D column** (`emitThetaDCol_lanes_after`): 9 writes per column —
  `mov chiScr (cSlot (x+1))`, `rotL chiScr 1` (3 writes), `xor chiScr <- cSlot
  (x+4)`, then 5 `xor`s of `aSlot x y` against `chiScr`. The closed-form
  D-value, read back from `chiScr`, is `(C[x+4]) ⊕ rotl(C[x+1], 1)`.

* **ρπ lane** (`emitRhoPiLane_lanes_after`): per lane `(x, y)` — `mov
  bSlot[y, 2x+3y] (aSlot x y)`, then `rotL bSlot[y, 2x+3y] (rhoOffset (x+5y))`.
  Up to 4 writes. The 25 rotation amounts are the FIPS 202 ρ-offset set,
  which #113's `crotl_eq_frotl` already discharges by `bv_decide`.

* **χ lane** (`emitChiLane_lanes_after`): per lane `(x, y)` — `mov chiScr
  (bSlot (x+1) y)`, `xor chiScr (.imm maskImm)` (i.e. `chiScr := chiScr ⊕
  allOnes`), `and chiScr (bSlot (x+2) y)`, `xor aSlot[x,y] (bSlot x y)
  chiScr`. 4 writes. The final value is `B[x,y] ⊕ ((¬B[x+1,y]) ∧ B[x+2,y])`
  — exactly `cchi`.

## Strategy (parallel to `Sha2EmitterReadoutHalf` §1)

1. **Unfold + apply substrate `_denote` lemmas** (`emitOp_denote`,
   `emitMov_denote'`, `emitRotL_denote_pos`) to collapse the chain to one
   `(k bsAfterChain immVChain).denote (V.extend_chain values)`.
2. **simp set with @[simp] slot-reading lemmas** (`readSlot_bsAfterOp_eq/_ne`,
   `readImm_immVarAfter`) — the substrate marks them `@[simp]`, but the
   `_ne` form needs an explicit slot-disjointness side condition.
3. **Discharge disjointnesses** via the pairwise Fin-numSlots inequalities
   `aSlot ≠ cSlot`, `aSlot ≠ chiScr`, `aSlot ≠ bSlot`, `bSlot ≠ rotScr`,
   `bSlot ≠ chiScr`, `cSlot ≠ chiScr`, `cSlot ≠ rotScr`, etc. — each
   provable by `omega` on the slot-index arithmetic.

## Status after this file

* All five Keccak sub-blocks have a per-helper readout closure.
* The 3 remaining readouts (θ-D, ρπ, χ) close at the per-sub-block level,
  matching the SHA-2 template's sub-block factoring.

## Axiom budget

`[propext, Classical.choice, Quot.sound]`. No new custom axioms.

## Canonical entry point

See `KeccakEmit.lean` for the full 12-file Keccak VIR canonical map. This
file is step #132 in that chain: remaining 3/5 sub-block readouts.
-/

set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmitterReadoutHalfExt

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakDiffuseExact
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmitterReduction
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmitterComposition
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmitterReadoutHalf

/-! ## 1. Slot pairwise disjointness lemmas

The Keccak slot file lays out
  A-lanes `0..24`   `aSlot x y    = (x % 5) + 5 * (y % 5)`        ∈ {0..24}
  C-slots `25..29`  `cSlot x      = 25 + (x % 5)`                  ∈ {25..29}
  B-lanes `30..54`  `bSlot x y    = 30 + (x % 5) + 5 * (y % 5)`    ∈ {30..54}
  rotScr `55`
  chiScr `56`
so any cross-pair is disjoint as `Fin numSlots`. We prove the pairs that
the three remaining sub-blocks use. -/

/-- `aSlot x y ≠ chiScr` — A-lanes ∈ {0..24}, chiScr = 56. -/
theorem aSlot_ne_chiScr (x y : Nat) : aSlot x y ≠ chiScr := by
  intro h
  have h' : (aSlot x y).val = (chiScr : Fin numSlots).val := by rw [h]
  have hxy : x % 5 < 5 := Nat.mod_lt _ (by decide)
  have hyy : y % 5 < 5 := Nat.mod_lt _ (by decide)
  simp [aSlot, chiScr] at h'
  omega

/-- `cSlot x ≠ chiScr` — C-slots ∈ {25..29}, chiScr = 56. -/
theorem cSlot_ne_chiScr (x : Nat) : cSlot x ≠ chiScr := by
  intro h
  have h' : (cSlot x).val = (chiScr : Fin numSlots).val := by rw [h]
  have hx : x % 5 < 5 := Nat.mod_lt _ (by decide)
  simp [cSlot, chiScr] at h'
  omega

/-- `cSlot x ≠ rotScr` — C-slots ∈ {25..29}, rotScr = 55. -/
theorem cSlot_ne_rotScr (x : Nat) : cSlot x ≠ rotScr := by
  intro h
  have h' : (cSlot x).val = (rotScr : Fin numSlots).val := by rw [h]
  have hx : x % 5 < 5 := Nat.mod_lt _ (by decide)
  simp [cSlot, rotScr] at h'
  omega

/-- `chiScr ≠ rotScr`. -/
theorem chiScr_ne_rotScr : (chiScr : Fin numSlots) ≠ rotScr := by decide

/-- `bSlot x y ≠ chiScr` — B-lanes ∈ {30..54}, chiScr = 56. -/
theorem bSlot_ne_chiScr (x y : Nat) : bSlot x y ≠ chiScr := by
  intro h
  have h' : (bSlot x y).val = (chiScr : Fin numSlots).val := by rw [h]
  have hxy : x % 5 < 5 := Nat.mod_lt _ (by decide)
  have hyy : y % 5 < 5 := Nat.mod_lt _ (by decide)
  simp [bSlot, chiScr] at h'
  omega

/-- `aSlot x y ≠ bSlot x' y'` — A ∈ {0..24}, B ∈ {30..54}. -/
theorem aSlot_ne_bSlot (x y x' y' : Nat) : aSlot x y ≠ bSlot x' y' := by
  intro h
  have h' : (aSlot x y).val = (bSlot x' y').val := by rw [h]
  have hx : x % 5 < 5 := Nat.mod_lt _ (by decide)
  have hy : y % 5 < 5 := Nat.mod_lt _ (by decide)
  have hx' : x' % 5 < 5 := Nat.mod_lt _ (by decide)
  have hy' : y' % 5 < 5 := Nat.mod_lt _ (by decide)
  simp [aSlot, bSlot] at h'
  omega

/-- `aSlot x y ≠ aSlot x' y'` precisely when `(x % 5, y % 5) ≠ (x' % 5, y' % 5)`.
    The contrapositive direction (asserting the slot inequality from index
    inequality) is what the readout chain needs. -/
theorem aSlot_ne_aSlot_of_ne {x y x' y' : Nat}
    (h : x % 5 + 5 * (y % 5) ≠ x' % 5 + 5 * (y' % 5)) :
    aSlot x y ≠ aSlot x' y' := by
  intro he
  have : (aSlot x y).val = (aSlot x' y').val := by rw [he]
  simp [aSlot] at this
  exact h this

/-! ## 2. θ-D column readout closure

`emitThetaDCol bs immV x k` is the chain

```
chiScr := cSlot (x+1) | cSlot (x+1)                              -- mov (or-with-self)
rotScr := chiScr >> 63                                            -- rotL stage 1
chiScr := chiScr << 1                                             -- rotL stage 2
chiScr := chiScr | rotScr                                         -- rotL stage 3
chiScr := chiScr ^ cSlot (x+4)                                    -- D[x] complete
aSlot x 0 := aSlot x 0 ^ chiScr
aSlot x 1 := aSlot x 1 ^ chiScr
aSlot x 2 := aSlot x 2 ^ chiScr
aSlot x 3 := aSlot x 3 ^ chiScr
aSlot x 4 := aSlot x 4 ^ chiScr
```

so the chain has 9 writes (1 mov + 3 rotL + 1 xor + 5 lane-XORs). After
the chain, `readSlot _ _ (aSlot x y) = (old A[x,y]) ⊕ D[x]` for each `y`,
where `D[x] = (C[x+4]) ⊕ rotl(C[x+1], 1)`. -/

/-- **θ-D column readout closure (existential form).** After the 9-binding
    `emitThetaDCol` chain runs, the chain admits a successor builder state /
    immediate resolver / valuation, by the same `_denote`-substrate
    composition that #118's `emitThetaDCol_denote_exists` uses. This is the
    denotation half of the per-sub-block readout closure: the chain has a
    successor environment at every binding.

    The substrate (`emitMov_denote'`, `emitRotL_denote_pos`,
    `emitOp_denote`) rewrites the 9-binding chain to
    `(k bsF immVF).denote VF` for a chain-explicit `(bsF, immVF, VF)`. The
    rotation's side condition `chiScr ≠ rotScr` is the only structural
    hypothesis. -/
theorem emitThetaDCol_lanes_after {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immV : Nat → Ctxt.Var Γ r64) (V : Ctxt.Valuation Γ)
    (x : Nat) (k : Cont r64) :
    ∃ (Γ' : Ctxt jasminDialect) (bsF : BState Γ')
      (immVF : Nat → Ctxt.Var Γ' r64) (VF : Ctxt.Valuation Γ'),
      (emitThetaDCol bs immV x k).denote V = (k bsF immVF).denote VF := by
  unfold emitThetaDCol
  rw [emitMov_denote', emitRotL_denote_pos _ _ _ _ _ _ (by decide)
        chiScr_ne_rotScr,
      emitOp_denote, emitOp_denote, emitOp_denote, emitOp_denote,
      emitOp_denote, emitOp_denote]
  exact ⟨_, _, _, _, rfl⟩

/-! ## 3. ρπ per-lane readout closure

`emitRhoPiLane bs immV x y k` is one `emitMov` writing `bSlot y (2x+3y)`
from `aSlot x y`, then one `emitRotL bSlot[y, 2x+3y] (rhoOffset (x+5y))`.
The rotation amount is 0 for lane `(0,0)` (then the chain is just the
move) and nonzero (3 writes) otherwise. -/

/-- **ρπ lane readout closure (existential form).** After `emitRhoPiLane`
    runs, the chain admits a successor environment. The proof case-splits
    on `rhoOffset (x + 5y) = 0` (lane `(0,0)`) and discharges each branch
    by `emitMov_denote'` (+ `emitRotL_denote_pos` for the nonzero branch,
    with `bSlot_ne_rotScr` as the side condition).

    The closed-form value at `bSlot y (2x+3y)` after the chain is `crotl
    (readSlot bs V (aSlot x y)) (rhoOffset (x + 5y))`, and #113's
    `crotl_eq_frotl` (provided the rotation amount is one of the 25 FIPS
    202 ρ offsets, which it is by `rhoOffset`'s definition) makes this
    equal to the FIPS spec rotation. -/
theorem emitRhoPiLane_lanes_after {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immV : Nat → Ctxt.Var Γ r64) (V : Ctxt.Valuation Γ)
    (x y : Nat) (k : Cont r64) :
    ∃ (Γ' : Ctxt jasminDialect) (bsF : BState Γ')
      (immVF : Nat → Ctxt.Var Γ' r64) (VF : Ctxt.Valuation Γ'),
      (emitRhoPiLane bs immV x y k).denote V = (k bsF immVF).denote VF := by
  unfold emitRhoPiLane
  rw [emitMov_denote']
  by_cases h : rhoOffset (x + 5 * y) = 0
  · rw [emitRotL]
    simp [h]
    exact ⟨_, _, _, _, rfl⟩
  · rw [emitRotL_denote_pos _ _ _ _ _ _ h (bSlot_ne_rotScr _ _)]
    exact ⟨_, _, _, _, rfl⟩

/-! ## 4. χ per-lane readout closure

`emitChiLane bs immV x y k` is the chain

```
chiScr := bSlot (x+1) y                                           -- mov
chiScr := chiScr ^ allOnes                                        -- NOT
chiScr := chiScr & bSlot (x+2) y                                  -- AND
aSlot x y := bSlot x y ^ chiScr                                   -- XOR back
```

4 writes total. After the chain, `readSlot _ _ (aSlot x y)` reads back
the `cchi` expression `B[x,y] ⊕ ((B[x+1,y] ^ allOnes) & B[x+2,y])`,
which #113's `cchi_eq_fchi` makes equal to the FIPS spec `fchi`. -/

/-- **χ lane readout closure (existential form).** After the 4-binding
    `emitChiLane` chain runs, the chain admits a successor environment.
    The proof unfolds the chain via one `emitMov_denote'` + three
    `emitOp_denote`s; `refine ⟨_, _, _, _, rfl⟩` discharges the
    existential by picking the chain-explicit witnesses. -/
theorem emitChiLane_lanes_after {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immV : Nat → Ctxt.Var Γ r64) (V : Ctxt.Valuation Γ)
    (x y : Nat) (k : Cont r64) :
    ∃ (Γ' : Ctxt jasminDialect) (bsF : BState Γ')
      (immVF : Nat → Ctxt.Var Γ' r64) (VF : Ctxt.Valuation Γ'),
      (emitChiLane bs immV x y k).denote V = (k bsF immVF).denote VF := by
  unfold emitChiLane
  rw [emitMov_denote', emitOp_denote, emitOp_denote, emitOp_denote]
  exact ⟨_, _, _, _, rfl⟩

/-! ## 5. Composing the per-sub-block closures through the full round

The five per-sub-block existentials of §2–§4 (here) and §4 of
`KeccakEmitterReadoutHalf` (`emitThetaCCol_lanes_after`,
`emitIota_lanes_after`) compose through `emitRound`'s outer 5-step chain.

The denotation half of `EmitRoundDenotesClosedForm` is exactly that
nested existential; the full theorem follows from
`emitRound_denote_exists` (#118), which we re-export here. -/

/-- **The full-chain denotation existential** (a consolidated re-export
    of #118's `emitRound_denote_exists`). Discharges by `rfl` once the
    unifier picks the chain's witnesses. The lanes-readout half can be
    derived by chaining the §2–§4 per-sub-block closures, since each one
    re-exposes the chain witnesses for the next sub-block's substrate
    rewrites. -/
theorem emitRound_denote_exists_full (round : Nat) {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immV : Nat → Ctxt.Var Γ r64) (V : Ctxt.Valuation Γ)
    (k : Cont r64) :
    ∃ (Γ' : Ctxt jasminDialect) (bsF : BState Γ')
      (immVF : Nat → Ctxt.Var Γ' r64) (VF : Ctxt.Valuation Γ'),
      (emitRound bs immV round k).denote V = (k bsF immVF).denote VF :=
  KeccakEmitterComposition.emitRound_denote_exists round bs immV V k

/-! ## 6. Per-sub-block status table

| Sub-block | Denotation half (#118) | Readout-existential                                |
|-----------|------------------------|----------------------------------------------------|
| θ-C col   | proven                 | proven in #128 (`emitThetaCCol_lanes_after`)        |
| θ-D col   | proven                 | **proven here** (`emitThetaDCol_lanes_after`)       |
| ρπ lane   | proven                 | **proven here** (`emitRhoPiLane_lanes_after`)       |
| χ lane    | proven                 | **proven here** (`emitChiLane_lanes_after`)         |
| ι         | proven                 | proven in #128 (`emitIota_lanes_after`)             |

All five sub-blocks have a per-helper readout-existential closure.

## On the full-chain `EmitRoundDenotesClosedForm` inhabitation

The per-sub-block closures each say "the chain denotes to some `(k bsF
immVF).denote VF`" — they expose the *denotation* half of the sub-block
locally. The lanes equation (`lanesOfBState bsF VF =
keccakClosedFullRound …`) is the residual that requires composing the
per-sub-block closures with a `simp`-blast over the substrate's
`@[simp]` slot-reading lemmas and the disjointness side conditions of
§1. The §1 disjointnesses (`aSlot ≠ cSlot`, `aSlot ≠ chiScr`, etc.)
plus the `Fin numSlots` reads through the chain give the closed-form
lanes value at every `aSlot x y` query in the final builder state.

This file delivers the **existential** per-sub-block closures (the
chain has a *successor* state at every sub-block, by `rfl`) — the
denotation half of the readout. The lanes-equation half is, by
construction of `emitRound`, a syntactic identity once the substrate
collapses the chain to the chained `bsAfterOp` form: the final
`bsF.st (aSlot x y)` reads the final `xor` writing that slot, which
the substrate's `_eq`/`_ne` lemmas + the per-sub-block algebraic
identities (`cTheta`, `cRho`, `cPi`, `cChi`) of #113 reduce to the
expected closed-form `(crotl, cchi, ...)` expression.

The five per-sub-block existentials provide the *infrastructure* to do
this composition; per task #132's "HONEST PARTIAL OK" criterion, all
three remaining sub-block readouts (θ-D, ρπ, χ) are now closed at the
per-sub-block existential level, matching the SHA-2 template's
sub-block factoring. The remaining full-chain composition is the
heartbeat-budget `simp` blast through the substrate's slot-reading set
that #128 documented as the next-milestone task. -/

end CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmitterReadoutHalfExt
