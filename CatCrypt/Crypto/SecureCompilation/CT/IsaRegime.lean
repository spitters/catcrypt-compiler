/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.CT.Leakage

@[expose] public section

set_option autoImplicit false

/-!
# Timing regimes of an instruction set

A timing regime is a hardware condition under which a vendor table of data-independent
instructions applies. `TimingRegime R Mnem` is the interface the regime types of the three
instruction sets share: `CT.DoitRegime` over `CT.X86Mnem` (Intel DOITM), `ArmRegime` over
`CT.ArmMnem` (`PSTATE.DIT = 1`) and `RvRegime` over `CT.RvMnem` (Zkt). A machine instance
takes a regime as a parameter, and a constant-time statement about the machine names the
regime it holds under.

The interface fixes the meaning of the two regimes every instruction set has. Under
`unguaranteed` every instruction other than a control transfer makes its data operands
observable. Under `guaranteed`, the regime the vendor specification gives, the operands of an
instruction are observable when the vendor table does not list it. No regime makes observable
an operand that `unguaranteed` hides, so a control transfer has no operand event under any
regime; its outcome is a branch event. The address of a memory access is an address event
under every regime and is no part of this interface.

## Main definitions

* `TimingRegime`: the interface.
* `addrEvents`, `dataEvents`: the address channel and the data channel of a trace.
* The instance for `DoitRegime` over `X86Mnem`.
-/

namespace CatCrypt.Crypto.SecureCompilation.CT

/-- **The timing regimes of an instruction set** with mnemonic table `Mnem`. `leaks r m`
    states that an instruction with mnemonic `m` makes its data operands observable under the
    regime `r`. -/
class TimingRegime (R : Type) (Mnem : outParam Type) where
  /-- Whether the data operands of the mnemonic are observable under the regime. -/
  leaks : R → Mnem → Bool
  /-- The control transfers of the table. -/
  isControl : Mnem → Bool
  /-- The regime of the vendor specification. -/
  guaranteed : R
  /-- The regime without a vendor timing guarantee. -/
  unguaranteed : R
  /-- Without a guarantee, every instruction other than a control transfer leaks its
      operands. -/
  leaks_unguaranteed : ∀ m, leaks unguaranteed m = !isControl m
  /-- No regime makes observable an operand that `unguaranteed` hides. -/
  leaks_le_unguaranteed : ∀ r m, leaks r m = true → leaks unguaranteed m = true

namespace TimingRegime

variable {R Mnem : Type} [TimingRegime R Mnem]

/-- A control transfer has no operand event under any regime. -/
theorem leaks_control (r : R) {m : Mnem} (h : isControl R m = true) : leaks r m = false := by
  cases hl : leaks r m with
  | false => rfl
  | true =>
      have h' := leaks_le_unguaranteed r m hl
      rw [leaks_unguaranteed, h] at h'
      cases h'

end TimingRegime

/-! ## The address channel and the data channel of a trace -/

/-- An address event. -/
def CTLeak.isAddr : CTLeak → Bool
  | .addr .. => true
  | _ => false

/-- **The address channel** of a trace: its address events, in order. -/
def addrEvents (t : List CTLeak) : List CTLeak := t.filter CTLeak.isAddr

/-- **The data channel** of a trace: its events other than address events, in order. -/
def dataEvents (t : List CTLeak) : List CTLeak := t.filter (fun e => !e.isAddr)

@[simp] theorem addrEvents_nil : addrEvents [] = [] := rfl

@[simp] theorem dataEvents_nil : dataEvents [] = [] := rfl

theorem addrEvents_append (t u : List CTLeak) :
    addrEvents (t ++ u) = addrEvents t ++ addrEvents u := List.filter_append ..

theorem dataEvents_append (t u : List CTLeak) :
    dataEvents (t ++ u) = dataEvents t ++ dataEvents u := List.filter_append ..

/-- The control transfers of the x86 table. -/
def X86Mnem.isControl (m : X86Mnem) : Bool :=
  match m.timing with
  | .control => true
  | _ => false

/-- **The x86 timing regimes**: `DoitRegime.doitm` is the regime of the Intel DOIT list. -/
instance : TimingRegime DoitRegime X86Mnem where
  leaks := DoitRegime.leaksOperands
  isControl := X86Mnem.isControl
  guaranteed := .doitm
  unguaranteed := .unguaranteed
  leaks_unguaranteed := fun m => by
    cases h : m.timing <;> simp [DoitRegime.leaksOperands, X86Mnem.isControl, h]
  leaks_le_unguaranteed := fun r m => by
    cases r <;> cases h : m.timing <;> simp [DoitRegime.leaksOperands, h]

end CatCrypt.Crypto.SecureCompilation.CT
