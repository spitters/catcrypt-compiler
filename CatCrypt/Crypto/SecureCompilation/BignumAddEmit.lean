/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.BignumCarryDecomp
public import CatCrypt.Crypto.SecureCompilation.X86Backend.BignumCarryDecomp
public meta import CatCrypt.Crypto.SecureCompilation.MultiLimbEmitBridge
public import CatCrypt.Crypto.SecureCompilation.MultiLimbEmitBridge

/-!
# An emitted multi-limb add proven against the multi-limb proof stack

> **`@kat-target`.** Hand-authored leaf block + direct `runBlock` proof — a KAT oracle /
> prototype for the bridge technique, NOT the canonical artifact. New field ops go via the
> golden path (`FieldEmitGoldenPath`; see `EMIT_PROVENANCE.md`); do not extend by hand.

The first emission whose `runBlock` value is proven equal — symbolically, for all
inputs — to a `MultiLimbKernel` function value (not a concrete `native_decide` and not
a KAT). A two-limb add-with-carry over the `JInstr`/`JState` x86 machine:

```
adcx a0, b0    -- a0 := a0 + b0 + CF,  CF := carry
adcx a1, b1    -- a1 := a1 + b1 + CF,  CF := carry
```

`add2adcx_value` proves the emitted block's two output limbs plus the carry-out bit
equal `valLimbs[a0,a1] + valLimbs[b0,b1]`, and `add2adcx_bignumVal` reads that through
`valLimbs_eq_bignumVal` as `bignumVal (addLimbs [a0,a1] [b0,b1] 0)` — the emitted x86
block computes exactly the verified multi-limb add. This is the `valLimbs(runBlock) =
bignumVal(kernel)` bridge a Barrett-reduce emission needs, exhibited on the add step.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.BignumAddEmit

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
open CatCrypt.Crypto.SecureCompilation.MultiLimbEmitBridge

/-- The two-limb add-with-carry kernel body over `JInstr 64` (carry-chained `adcx`). -/
def add2adcxBlock : List (JInstr 64) :=
  [ .adcx "a0" (.reg "b0"), .adcx "a1" (.reg "b1") ]

/-- The pure-arithmetic reassembly of a two-limb carry chain (small symbolic powers,
    so `omega` handles it cleanly without the machine-state numerals). -/
theorem reassemble (u0 u1 a0 b0 a1 b1 : Nat) (k0 k1 : Bool)
    (hd0 : u0 + 2 ^ 64 * (if k0 = true then 1 else 0)
      = a0 + b0 + (if (false = true) then 1 else 0))
    (hd1 : u1 + 2 ^ 64 * (if k1 = true then 1 else 0) = a1 + b1 + (if k0 = true then 1 else 0)) :
    u0 + 2 ^ 64 * u1 + (if k1 = true then 1 else 0) * 2 ^ 128
      = a0 + 2 ^ 64 * a1 + (b0 + 2 ^ 64 * b1) := by
  cases k0 <;> cases k1 <;> simp only [Bool.false_eq_true, reduceIte] at * <;> omega

/-- **Symbolic value-correctness of the emitted block.** With `CF` cleared on entry,
    the two output limbs plus the carry-out equal the sum of the input two-limb
    values — for all inputs, over the differentially-validated x86 machine. -/
theorem add2adcx_value (s : JState 64) (hcf : s.flagB (·.cf) = false) :
    valLimbs [(runBlock s add2adcxBlock).get "a0", (runBlock s add2adcxBlock).get "a1"]
        + (if (runBlock s add2adcxBlock).flagB (·.cf) then 1 else 0) * 2 ^ 128
      = valLimbs [s.get "a0", s.get "a1"] + valLimbs [s.get "b0", s.get "b1"] := by
  have hrun : runBlock s add2adcxBlock
      = evalInstr (evalInstr s (.adcx "a0" (.reg "b0"))) (.adcx "a1" (.reg "b1")) := rfl
  have hcf' : (Option.getD s.flags.cf false) = false := hcf
  -- the two carry-chain decompositions (low word + carry reassemble the true sum)
  have hd0 := waddcarry_decompose (s.get "a0") (s.get "b0") (Option.getD s.flags.cf false)
  have hd1 := waddcarry_decompose (s.get "a1") (s.get "b1")
    (waddcarry (s.get "a0") (s.get "b0") (Option.getD s.flags.cf false)).1
  rw [hrun]
  simp only [valLimbs, get_adcx, cf_adcx, JOperand.eval, JState.flagB,
    String.reduceEq, reduceIte, Option.getD_some, mul_zero, add_zero]
  rw [hcf'] at hd0 hd1 ⊢
  -- everything is now in terms of the two `waddcarry` low words and carries
  generalize (waddcarry (s.get "a0") (s.get "b0") false).1 = k0 at *
  generalize (waddcarry (s.get "a0") (s.get "b0") false).2.toNat = u0 at *
  generalize (waddcarry (s.get "a1") (s.get "b1") k0).1 = k1 at *
  generalize (waddcarry (s.get "a1") (s.get "b1") k0).2.toNat = u1 at *
  exact reassemble u0 u1 (s.get "a0").toNat (s.get "b0").toNat (s.get "a1").toNat
    (s.get "b1").toNat k0 k1 hd0 hd1

/-- **The emitted block computes the verified multi-limb add.** Reading the value
    identity through `valLimbs_eq_bignumVal`, the emitted output limbs plus carry
    equal `bignumVal (addLimbs [a0,a1] [b0,b1] 0)` — the kernel-proven full sum. -/
theorem add2adcx_bignumVal (s : JState 64) (hcf : s.flagB (·.cf) = false) :
    bignumVal [(runBlock s add2adcxBlock).get "a0", (runBlock s add2adcxBlock).get "a1"]
        + (if (runBlock s add2adcxBlock).flagB (·.cf) then 1 else 0) * 2 ^ 128
      = bignumVal (addLimbs [s.get "a0", s.get "a1"] [s.get "b0", s.get "b1"] 0) := by
  rw [addLimbs_val [s.get "a0", s.get "a1"] [s.get "b0", s.get "b1"] 0 (by decide) rfl,
    ← valLimbs_eq_bignumVal, ← valLimbs_eq_bignumVal, ← valLimbs_eq_bignumVal]
  have h := add2adcx_value s hcf
  simpa using h

end CatCrypt.Crypto.SecureCompilation.BignumAddEmit
