/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.LowCT

/-!
# Explicit variable-time-operation detector

The VIR-level CT predicate (`SecureCompilation/VIR/CTPredicate.lean`) and the
`LowCT` taint analyser reject **data-dependent control flow** and
**data-dependent memory indices**. They do *not* yet name the third classical
constant-time hazard: a **variable-time arithmetic operation** whose latency
depends on the *value* of a secret operand — division, remainder/modulo,
data-dependent (variable-length) shift, an early-terminating multiply, or a
secret-dependent comparison with an early exit.

Today this is covered only *implicitly*: `CatCryptOp` (and the `LowCT` IR) have
no division op, so the hazard cannot be expressed and therefore never fires.
That is fragile — adding a `div`/`mod`/`vshift` op later would silently slip a
variable-time leak past the analyser. This module makes the rule **explicit**,
so any future op addition that is variable-time must be classified here (and the
keystone below then forbids it on secret operands by construction).

## What this module establishes

An abstract instruction model `VInstr` carrying an operation `VOp` and the
secrecy levels (`SecretLevel`) of its operands, plus:

* `VOp.varTime` — the classification: which operations are variable-time.
* A leakage / timing model `VInstr.timing`: a variable-time op leaks (a function
  of) its operand values; a constant-time op has fixed timing.
* **Keystone** `varTimeOp_secret_not_ct`: an instruction whose op is variable-
  time and at least one operand is `Secret` is **not** constant-time — its
  timing is value-dependent on a secret. Stated as a genuine non-CT witness:
  two operand assignments that agree on all public slots can still differ in the
  observed timing (`¬ VInstr.ctSafe`, and a concrete leaking pair).
* **Public-accepted dual** `varTimeOp_public_accepted`: a variable-time op with
  *all-Public* operands is accepted — the leak is ≤ the (already public) inputs,
  exactly the declassified / public-input regime of
  `VartimeBignumInverse.lean`'s `vartimeInvertBody_accepted_public`.
* A detector `hasSecretVarTimeOp : Program → Bool` over a straight-line program,
  and `hasSecretVarTimeOp_false_of_ct`: a CT program contains no secret
  variable-time op.

## Honesty ledger

This is an **abstract** instruction model (op tag + operand levels + an abstract
value→timing leakage function), in the negative-witness style of
`CTPredicate.lean` and the accept/reject duals of `VartimeBignumInverse.lean`.
It is *not yet wired into* `catCryptDialect`/`LowCT` (those IRs have no var-time
op to classify — which is precisely the gap this hardens against). When a
variable-time op is added to either IR, route its classification through
`VOp.varTime` and discharge its CT obligation via `varTimeOp_secret_not_ct` /
`varTimeOp_public_accepted`. Dialect wiring is the follow-up.
-/

namespace CatCrypt.Crypto.SecureCompilation.VarTimeOpDetector

open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)

set_option autoImplicit false

/-! ## §1. The operation set and the variable-time classification -/

/-- An abstract arithmetic / logical operation, partitioned into the
constant-time core and the four classical variable-time hazards.

The variable-time constructors are exactly the ops whose hardware latency is a
function of operand *values* (not just operand widths):

* `div` / `mod` — integer division and remainder: the iteration count of a
  restoring/non-restoring divider depends on the magnitude of the operands.
* `vshift` — a *variable-length* (data-dependent count) shift on a target whose
  barrel shifter is not single-cycle, or a software emulated shift.
* `mulEarlyExit` — an early-terminating multiply (e.g. Booth recoding that
  short-circuits on leading zeros), latency a function of the multiplier value.
* `cmpEarlyExit` — a comparison / search with a data-dependent early exit
  (e.g. `memcmp`-style first-difference return), latency a function of where the
  first differing byte lies.

Everything else (`add`, `mul` for a fixed-latency multiplier, `xorOp`, `andOp`,
a *constant*-count shift `shiftConst`) is constant-time. -/
inductive VOp where
  | add : VOp
  | mul : VOp
  | xorOp : VOp
  | andOp : VOp
  | shiftConst : VOp
  -- variable-time hazards:
  | div : VOp
  | mod : VOp
  | vshift : VOp
  | mulEarlyExit : VOp
  | cmpEarlyExit : VOp
  deriving DecidableEq, Repr, Inhabited, BEq

/-- The variable-time classification: `true` for ops whose latency depends on
operand *values*. **This is the single point of truth** — any op added to `VOp`
that is value-time-dependent must return `true` here, and the keystone then
forbids it on a secret operand by construction. -/
def VOp.varTime : VOp → Bool
  | .div => true
  | .mod => true
  | .vshift => true
  | .mulEarlyExit => true
  | .cmpEarlyExit => true
  | _ => false

@[simp] theorem VOp.varTime_add : VOp.varTime .add = false := rfl
@[simp] theorem VOp.varTime_mul : VOp.varTime .mul = false := rfl
@[simp] theorem VOp.varTime_xorOp : VOp.varTime .xorOp = false := rfl
@[simp] theorem VOp.varTime_andOp : VOp.varTime .andOp = false := rfl
@[simp] theorem VOp.varTime_shiftConst : VOp.varTime .shiftConst = false := rfl
@[simp] theorem VOp.varTime_div : VOp.varTime .div = true := rfl
@[simp] theorem VOp.varTime_mod : VOp.varTime .mod = true := rfl
@[simp] theorem VOp.varTime_vshift : VOp.varTime .vshift = true := rfl
@[simp] theorem VOp.varTime_mulEarlyExit : VOp.varTime .mulEarlyExit = true := rfl
@[simp] theorem VOp.varTime_cmpEarlyExit : VOp.varTime .cmpEarlyExit = true := rfl

/-! ## §2. The abstract instruction and its operand secrecy levels -/

/-- An abstract instruction: an operation together with the secrecy
classification (`SecretLevel`) of each of its operands. The list `argLevels`
is the per-operand level; an empty list models a nullary op. -/
structure VInstr where
  op : VOp
  argLevels : List SecretLevel
  deriving Repr, Inhabited

/-- The instruction has at least one `Secret` operand. -/
def VInstr.hasSecretArg (i : VInstr) : Bool :=
  i.argLevels.any (· == SecretLevel.Secret)

/-- The detector's per-instruction flag: a variable-time op with a secret
operand — the hazard this module names. -/
def VInstr.isSecretVarTime (i : VInstr) : Bool :=
  i.op.varTime && i.hasSecretArg

/-! ## §3. The timing / leakage model

A variable-time op's *latency* is a function of its operand **values**; a
constant-time op's latency is fixed. We model an operand assignment as a map
from operand index to its (abstract) value, and `timing` as the observable
latency. The only structural fact we need is: for a variable-time op, `timing`
is allowed to depend on the value at *any* operand slot; for a CT op it is the
constant `1`. -/

/-- An operand-value assignment: index → abstract value. -/
abbrev ValAssign := Nat → Nat

/-- The observable timing of an instruction under a value assignment.

* Constant-time ops: fixed latency `1`, **independent** of `vals`.
* Variable-time ops: latency `1 + (sum of operand values)` — the canonical
  "latency is a function of the operand values" leakage shape. The exact
  function is immaterial; what matters (and what the keystone uses) is that it
  is *not constant* in the operand values. -/
def VInstr.timing (i : VInstr) (vals : ValAssign) : Nat :=
  if i.op.varTime then
    1 + (List.range i.argLevels.length).foldl (fun acc k => acc + vals k) 0
  else
    1

/-- A CT op's timing is independent of the operand values. -/
theorem VInstr.timing_const_of_not_varTime (i : VInstr)
    (h : i.op.varTime = false) (vals : ValAssign) :
    i.timing vals = 1 := by
  simp [VInstr.timing, h]

/-! ## §4. Constant-time-safety of an instruction (value-independence on public)

An instruction is **constant-time-safe** when its observable timing is
unchanged by any pair of operand-value assignments that agree on every *public*
operand slot — i.e. its timing leaks nothing beyond the public operands. This
is the standard observational definition specialised to one instruction. -/

/-- Two value assignments agree on the public operands of `i`: they coincide at
every index whose operand level is `Public`. -/
def PublicAgree (i : VInstr) (v1 v2 : ValAssign) : Prop :=
  ∀ k, k < i.argLevels.length →
    i.argLevels[k]? = some SecretLevel.Public → v1 k = v2 k

/-- **Constant-time-safety of an instruction.** Its timing depends only on the
public operands: any two assignments agreeing on the public slots produce the
same observable timing. -/
def VInstr.ctSafe (i : VInstr) : Prop :=
  ∀ v1 v2 : ValAssign, PublicAgree i v1 v2 → i.timing v1 = i.timing v2

/-! ## §5. Keystone: a variable-time op with a secret operand is NOT CT -/

/-- A CT op (any op that is not variable-time) is always `ctSafe`: its timing is
the constant `1`, hence trivially independent of operands. -/
theorem ctSafe_of_not_varTime (i : VInstr) (h : i.op.varTime = false) :
    i.ctSafe := by
  intro v1 v2 _
  rw [VInstr.timing_const_of_not_varTime i h,
      VInstr.timing_const_of_not_varTime i h]

/-- A variable-time op with **all-Public** operands is `ctSafe`: every operand
slot is public, so `PublicAgree` forces the two assignments to coincide on all
slots in range, and the timing (a function of exactly those values) is equal.

This is the *public-accepted dual* — the declassified / public-input regime: a
variable-time op is licensed when its operands are public, mirroring
`VartimeBignumInverse.vartimeInvertBody_accepted_public`. -/
theorem varTimeOp_public_accepted (i : VInstr)
    (hpub : ∀ l ∈ i.argLevels, l = SecretLevel.Public) :
    i.ctSafe := by
  intro v1 v2 hagree
  unfold VInstr.timing
  by_cases hvt : i.op.varTime
  · simp only [hvt, if_pos]
    -- the folds are equal because v1 k = v2 k for every k < length
    have hfold : ∀ k, k < i.argLevels.length → v1 k = v2 k := by
      intro k hk
      refine hagree k hk ?_
      have hmem : i.argLevels[k]? = some (i.argLevels[k]'hk) := by
        rw [List.getElem?_eq_getElem hk]
      rw [hmem, hpub _ (List.getElem_mem hk)]
    congr 1
    -- foldl over range length with v1 = foldl with v2
    have : ∀ n, n ≤ i.argLevels.length →
        (List.range n).foldl (fun acc k => acc + v1 k) 0
          = (List.range n).foldl (fun acc k => acc + v2 k) 0 := by
      intro n hn
      induction n with
      | zero => simp
      | succ m ih =>
        rw [List.range_succ, List.foldl_append, List.foldl_append,
            ih (Nat.le_of_succ_le hn)]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [hfold m (Nat.lt_of_succ_le hn)]
    exact this i.argLevels.length (le_refl _)
  · simp only [hvt, if_neg, Bool.not_eq_true] at *

/-- **KEYSTONE — a variable-time op with a secret operand is NOT constant-time.**

If the op is variable-time and some operand slot is `Secret`, then the
instruction is not `ctSafe`: we exhibit two operand-value assignments that agree
on every public slot yet produce **different** observable timings (they differ
only at the secret slot). The timing therefore leaks the secret operand's value
— exactly the variable-time-leak hazard.

This is the negative witness, in the style of `CTPredicate`'s non-CT flagging
and `VartimeBignumInverse.vartimeInvertBody_secret_rejected`: a secret-dependent
variable-time op is rejected, fail-closed. -/
theorem varTimeOp_secret_not_ct (i : VInstr)
    (hvt : i.op.varTime = true)
    (hsec : SecretLevel.Secret ∈ i.argLevels) :
    ¬ i.ctSafe := by
  -- Find the secret slot index.
  obtain ⟨j, hj, hjval⟩ := List.getElem_of_mem hsec
  intro hct
  -- Two assignments: all-zero, vs. 1 at the secret slot j.
  let v1 : ValAssign := fun _ => 0
  let v2 : ValAssign := fun k => if k = j then 1 else 0
  -- They agree on every public slot (they differ only at j, which is Secret).
  have hagree : PublicAgree i v1 v2 := by
    intro k hk hkpub
    -- at k = j the operand is Secret, contradicting hkpub
    by_cases hkj : k = j
    · subst hkj
      have : i.argLevels[k]? = some SecretLevel.Secret := by
        rw [List.getElem?_eq_getElem hk, hjval]
      rw [this] at hkpub
      exact absurd hkpub (by simp)
    · simp only [v1, v2, if_neg hkj]
  -- But the timings differ: the fold sees the extra 1 at slot j.
  have hne : i.timing v1 ≠ i.timing v2 := by
    simp only [VInstr.timing, hvt, if_true]
    -- fold with v1 (all 0) = 0; fold with v2 = 1 (only slot j contributes, j < length)
    have hf1 : (List.range i.argLevels.length).foldl (fun acc k => acc + v1 k) 0 = 0 := by
      have : ∀ n, (List.range n).foldl (fun acc k => acc + v1 k) 0 = 0 := by
        intro n; induction n with
        | zero => simp
        | succ m ih => rw [List.range_succ, List.foldl_append, ih]; simp [v1]
      exact this _
    have hf2 : (List.range i.argLevels.length).foldl (fun acc k => acc + v2 k) 0 = 1 := by
      -- exactly the j-th term is 1, all others 0; j < length
      have hgen : ∀ n, j < n →
          (List.range n).foldl (fun acc k => acc + v2 k) 0 = 1 := by
        intro n hjn
        induction n with
        | zero => omega
        | succ m ih =>
          rw [List.range_succ, List.foldl_append]
          rcases Nat.lt_or_ge j m with hlt | hge
          · rw [ih hlt]; simp only [List.foldl_cons, List.foldl_nil, v2]
            rw [if_neg (by omega)]
          · -- j = m
            have hjm : j = m := by omega
            have hf0 : (List.range m).foldl (fun acc k => acc + v2 k) 0 = 0 := by
              have hz : ∀ p, p ≤ m →
                  (List.range p).foldl (fun acc k => acc + v2 k) 0 = 0 := by
                intro p hp; induction p with
                | zero => simp
                | succ q ihq =>
                  rw [List.range_succ, List.foldl_append, ihq (Nat.le_of_succ_le hp)]
                  simp only [List.foldl_cons, List.foldl_nil, v2]
                  rw [if_neg (by omega)]
              exact hz m (le_refl _)
            rw [hf0]; simp only [List.foldl_cons, List.foldl_nil, v2]
            rw [if_pos hjm.symm]
      exact hgen _ hj
    rw [hf1, hf2]; omega
  exact hne (hct v1 v2 hagree)

/-! ## §6. The detector over a straight-line program -/

/-- A straight-line program is a list of abstract instructions. -/
abbrev Program := List VInstr

/-- **The detector.** `true` iff the program contains some variable-time op
applied to a secret operand. This is the static check that names the hazard. -/
def hasSecretVarTimeOp (p : Program) : Bool :=
  p.any VInstr.isSecretVarTime

@[simp] theorem hasSecretVarTimeOp_nil : hasSecretVarTimeOp [] = false := rfl

@[simp] theorem hasSecretVarTimeOp_cons (i : VInstr) (p : Program) :
    hasSecretVarTimeOp (i :: p)
      = (i.isSecretVarTime || hasSecretVarTimeOp p) := by
  simp [hasSecretVarTimeOp]

/-- **A program-level CT predicate.** Every instruction is `ctSafe`. -/
def Program.ctSafe (p : Program) : Prop :=
  ∀ i ∈ p, i.ctSafe

/-- **A CT program contains no secret variable-time op.** If every instruction
is constant-time-safe, the detector reports `false`: there is no variable-time
op on a secret operand, because such an op is provably not `ctSafe`
(`varTimeOp_secret_not_ct`). The detector is therefore *sound* — it never misses
a hazard that `ctSafe` rules out. -/
theorem hasSecretVarTimeOp_false_of_ct (p : Program) (h : Program.ctSafe p) :
    hasSecretVarTimeOp p = false := by
  simp only [hasSecretVarTimeOp, List.any_eq_false]
  intro i hi
  rw [Bool.not_eq_true]
  by_contra hsv
  rw [Bool.not_eq_false] at hsv
  -- i is a secret var-time op, so it is NOT ctSafe — contradicting h i.
  simp only [VInstr.isSecretVarTime, Bool.and_eq_true] at hsv
  obtain ⟨hvt, hhas⟩ := hsv
  have hsec : SecretLevel.Secret ∈ i.argLevels := by
    unfold VInstr.hasSecretArg at hhas
    rw [List.any_eq_true] at hhas
    obtain ⟨l, hlmem, hleq⟩ := hhas
    have : l = SecretLevel.Secret := by
      cases l
      · exact absurd hleq (by decide)
      · rfl
    rwa [this] at hlmem
  exact varTimeOp_secret_not_ct i hvt hsec (h i hi)

/-- Contrapositive convenience: if the detector fires, some instruction is not
`ctSafe`. -/
theorem not_ctSafe_of_hasSecretVarTimeOp (p : Program)
    (h : hasSecretVarTimeOp p = true) : ¬ Program.ctSafe p := by
  intro hct
  rw [hasSecretVarTimeOp_false_of_ct p hct] at h
  exact Bool.noConfusion h

/-! ## §7. Smoke tests -/

/-- A `div` with a secret divisor is flagged. -/
example :
    hasSecretVarTimeOp [⟨.div, [SecretLevel.Public, SecretLevel.Secret]⟩] = true := by
  decide

/-- A `div` with all-public operands is *not* flagged (public-input regime). -/
example :
    hasSecretVarTimeOp [⟨.div, [SecretLevel.Public, SecretLevel.Public]⟩] = false := by
  decide

/-- A constant-time `add` with a secret operand is *not* flagged. -/
example :
    hasSecretVarTimeOp [⟨.add, [SecretLevel.Secret, SecretLevel.Secret]⟩] = false := by
  decide

/-- The all-public `div` instruction is provably `ctSafe`. -/
example : VInstr.ctSafe ⟨.div, [SecretLevel.Public, SecretLevel.Public]⟩ :=
  varTimeOp_public_accepted _ (by intro l hl; fin_cases hl <;> rfl)

/-- A secret-divisor `div` instruction is provably NOT `ctSafe`. -/
example : ¬ VInstr.ctSafe ⟨.div, [SecretLevel.Public, SecretLevel.Secret]⟩ :=
  varTimeOp_secret_not_ct _ rfl (by simp)

end CatCrypt.Crypto.SecureCompilation.VarTimeOpDetector
