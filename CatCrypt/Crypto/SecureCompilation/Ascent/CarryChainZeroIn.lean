/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CarryChainTie

/-!
# A zero carry-in for the carry chain

`CarryChainTie.lowerCarryBlock_tie` runs a carry chain from a state whose `CF`
already holds the value of the chain's entry carry variable, an assumption
carried in `CarryInterp`. This module establishes that assumption at the value
`0` with the machine instruction `clc`, and composes: a chain prefixed by `clc`
satisfies the tie for every entry state, whatever its incoming carry flag.

## The prefix

`JInstr.clc` is the machine model's `Ox86_CLC_instr`: `CF := 0`, no other flag
and no register. `clearCarry` is the one-instruction block containing it.
`carryInterp_clearCarry` states that running it from a state satisfying the
register axis `JStateInterpG` alone yields `CarryInterp` at any carry variable
whose value under the valuation is `0`.

## Scope

* The prefix establishes the carry axis of `CarryInterp` and preserves the
  register axis. It says nothing about the other four flags, which `CarryInterp`
  does not constrain either.
* The entry carry variable's value `0` is a hypothesis on the valuation, not on
  the machine state: the correspondence is between a dialect chain whose entry
  carry is the literal zero and its machine run. A chain entered at a nonzero
  carry needs `stc`, the `JInstr` arm for `CF := 1`, which is not treated here.
* The lowering is `clc`, not the `xor dst, dst` idiom. Both clear `CF`; the
  `xor` form additionally writes a register and the other four flags, so it
  needs a fresh destination and a register-frame argument that `clc` does not.
* The witness fixes a two-limb chain, one fresh-register stream and one entry
  state. It is a value check on those, not a statement about the family.
* The prefixed and unprefixed runs are compared over `CarryChainTie.wG`, by
  evaluation. `wG` takes the value `d1` at every index above zero, so it is not
  injective and does not satisfy `FreshFor`; the tie route uses `dStream`
  instead, which does.

## What is proved

* `clearCarry`, `clearCarry_cf`, `clearCarry_get` — the prefix, the flag it
  writes and its register frame.
* `carryInterp_clearCarry` — the prefix establishes `CarryInterp` at a carry
  variable valued `0`.
* `lowerCarryBlock_zeroIn_tie` — the block tie for `clearCarry ++
  lowerCarryBlock …`, with no hypothesis on the entry carry flag.
* `dStream`, `dStream_freshFor` — an injective fresh-register stream disjoint
  from the witness register map.
* `boundaryVal`, `cfSetState`, `twoLimbZeroIn`, `twoLimbCfSetPrefixed`,
  `twoLimbCfSetUnprefixed` — a two-limb witness entered with `CF` set, whose low
  limb wraps exactly when the carry-in is `1`: the prefixed run gives `12`, the
  unprefixed run `13`.

@ascent-fixture theorems: clearCarry_cf, carryInterp_clearCarry
`clearCarry` is the one-instruction prefix whose effect on the carry flag these
theorems state, so the chain's carry-in assumption is discharged rather than
assumed. It encodes no bytes that ship.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.CarryChain

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent

/-! ## 1. The clearing prefix -/

/-- The machine block that clears the carry flag: the single `clc`. -/
def clearCarry : List (JInstr 64) := [.clc]

/-- The flag `clc` writes: `CF` is `false` after the prefix, from any state. -/
theorem clearCarry_cf (s : JState 64) :
    (runBlock s clearCarry).flagB (·.cf) = false := rfl

/-- The register frame of the prefix: `clc` writes no register. -/
theorem clearCarry_get (r : String) (s : JState 64) :
    (runBlock s clearCarry).get r = s.get r := rfl

/-- **The prefix establishes the entry condition.** From a state satisfying the
    register axis alone, running `clearCarry` gives the two-axis correspondence
    `CarryInterp` at a carry variable whose value under `V` is `0`. The incoming
    carry flag of `s` is unconstrained. -/
theorem carryInterp_clearCarry {Γ : Ctxt jasminDialect} (ρ : RegMapG Γ)
    (c : Ctxt.Var Γ (.reg 1)) (V : Ctxt.Valuation Γ) (s : JState 64)
    (hreg : JStateInterpG ρ V s) (hzero : c.lookup V = (0 : BitVec 1)) :
    CarryInterp ρ c V (runBlock s clearCarry) := by
  refine ⟨fun v => ?_, ?_⟩
  · rw [clearCarry_get (ρ v) s]; exact hreg v
  · rw [clearCarry_cf s, hzero]; rfl

/-! ## 2. The tie with no assumption on the entry flag -/

/-- **The block tie for a carry chain entered at carry zero.** For a chain whose
    entry carry variable is valued `0`, prefixing the lowering with `clc` ties the
    machine run to the chain's `Com jasminDialect` denotation from an arbitrary
    entry state: only the register axis `JStateInterpG` is assumed, and the
    entry carry flag is arbitrary. -/
theorem lowerCarryBlock_zeroIn_tie {Γ : Ctxt jasminDialect}
    {c : Ctxt.Var Γ (.reg 1)} (block : CarryBlock Γ c) (ρ : RegMapG Γ)
    (g : Nat → String) (s : JState 64) (V : Ctxt.Valuation Γ)
    (hreg : JStateInterpG ρ V s) (hzero : c.lookup V = (0 : BitVec 1))
    (hfresh : FreshFor ρ g) :
    (runBlock s (clearCarry ++ lowerCarryBlock block ρ g)).get
        (outRegC block ρ g)
      = block.toCom.denote V := by
  rw [runBlock_append]
  exact lowerCarryBlock_tie block ρ g _ V
    (carryInterp_clearCarry ρ c V s hreg hzero) hfresh

/-! ## 3. A fresh-register stream for the witness

`FreshFor` demands an injective stream disjoint from the register map's range.
`dStream k` is `d` followed by `k` copies of `x`, so injectivity is a length
argument and disjointness from the witness map's four registers is a first-letter
argument. -/

/-- The fresh-register stream `d`, `dx`, `dxx`, … -/
def dStream : Nat → String := fun k => String.ofList ('d' :: List.replicate k 'x')

/-- `dStream` is injective. -/
theorem dStream_injective (i j : Nat) (h : i ≠ j) : dStream i ≠ dStream j := by
  intro heq
  exact h (by simpa using String.ofList_inj.mp heq)

/-- No name in the stream is one of the witness map's registers: those begin with
    `a` or `b`, every stream name with `d`. -/
theorem dStream_ne_wRho (i : Nat) (v : Ctxt.Var Γw (.reg 64)) :
    dStream i ≠ wRho v := by
  match v with
  | .there .here =>
      show dStream i ≠ "a0"
      intro h; simp only [dStream] at h; simpa using congrArg String.toList h
  | .there (.there .here) =>
      show dStream i ≠ "b0"
      intro h; simp only [dStream] at h; simpa using congrArg String.toList h
  | .there (.there (.there .here)) =>
      show dStream i ≠ "a1"
      intro h; simp only [dStream] at h; simpa using congrArg String.toList h
  | .there (.there (.there (.there .here))) =>
      show dStream i ≠ "b1"
      intro h; simp only [dStream] at h; simpa using congrArg String.toList h

/-- The fresh invariant for the witness register map and stream. -/
theorem dStream_freshFor : FreshFor wRho dStream :=
  ⟨dStream_injective, fun i v => dStream_ne_wRho i v⟩

/-! ## 4. The two-limb witness entered with `CF` set

The low limb adds `2 ^ 64 - 1` and `0`. That sum wraps exactly when the carry-in
is `1`, so the high limb's result reads `5 + 7 + 1 = 13` from an uncleared flag
and `5 + 7 + 0 = 12` from a cleared one. -/

/-- The witness valuation: entry carry `0`, low limbs `2 ^ 64 - 1` and `0`, high
    limbs `5` and `7`. -/
def boundaryVal : Ctxt.Valuation Γw :=
  .cons (0 : BitVec 1)
    (.cons (BitVec.ofNat 64 (2 ^ 64 - 1))
      (.cons (0 : BitVec 64)
        (.cons (5 : BitVec 64) (.cons (7 : BitVec 64) .nil))))

/-- The witness machine state: the four limb operands in the registers `wRho`
    names, and the carry flag **set** on entry. -/
def cfSetState : JState 64 :=
  { regs := fun r =>
      if r = "a0" then BitVec.ofNat 64 (2 ^ 64 - 1) else
      if r = "b0" then 0 else
      if r = "a1" then 5 else
      if r = "b1" then 7 else 0
    flags := { cf := some true } }

/-- The register axis holds between `cfSetState` and `boundaryVal` under `wRho`.
    The carry axis does not: the state's `CF` is `true` and the valuation's entry
    carry is `0`. -/
theorem cfSetState_interp : JStateInterpG wRho boundaryVal cfSetState := by
  intro v
  match v with
  | .there .here => rfl
  | .there (.there .here) => rfl
  | .there (.there (.there .here)) => rfl
  | .there (.there (.there (.there .here))) => rfl

/-- The witness chain's denotation: the low limb does not wrap at carry-in `0`,
    so the high limb is `5 + 7`. -/
theorem twoLimbBlock_denote_boundaryVal :
    twoLimbBlock.toCom.denote boundaryVal = (12 : BitVec 64) := rfl

/-- **The witness for the zero carry-in tie.** From an entry state whose `CF` is
    set, the prefixed lowering of the two-limb chain reads `12`: the denotation
    of the chain at entry carry `0`. -/
theorem twoLimbZeroIn :
    (runBlock cfSetState
        (clearCarry ++ lowerCarryBlock twoLimbBlock wRho dStream)).get
        (outRegC twoLimbBlock wRho dStream) = (12 : BitVec 64) := by
  rw [lowerCarryBlock_zeroIn_tie twoLimbBlock wRho dStream cfSetState boundaryVal
    cfSetState_interp rfl dStream_freshFor]
  exact twoLimbBlock_denote_boundaryVal

/-- The entry carry flag is observable in the chain's output: run from the same
    state without the prefix, the lowered chain reads `13`, the high limb taken
    at carry-in `1`. Stated over `CarryChainTie.wG`, whose two names evaluate,
    and checked by evaluation rather than through the tie. -/
theorem twoLimbCfSetUnprefixed :
    (runBlock cfSetState (lowerCarryBlock twoLimbBlock wRho wG)).get
        (outRegC twoLimbBlock wRho wG) = (13 : BitVec 64) := by
  decide

/-- The same run with the clearing prefix reads `12`, the companion of
    `twoLimbCfSetUnprefixed` over the same fresh-name stream. -/
theorem twoLimbCfSetPrefixed :
    (runBlock cfSetState (clearCarry ++ lowerCarryBlock twoLimbBlock wRho wG)).get
        (outRegC twoLimbBlock wRho wG) = (12 : BitVec 64) := by
  decide

end CatCrypt.Crypto.SecureCompilation.Ascent.CarryChain
