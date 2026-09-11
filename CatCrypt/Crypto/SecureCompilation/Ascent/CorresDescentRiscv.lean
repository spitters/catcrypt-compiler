/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresDescentX86
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresRiscv

/-!
# The descent's `Refines` as an ascent correspondence at the RV64 machine

The RV64 twin of `CorresDescentX86`: the fragment the relational compiler
certifies by `Refines spec frag`, closed at slot `dst` and compiled through
`comToRegProg`, `regToROp` and `lowerRBlock64`, is a forward simulation at the
abstract step `spec` over `runRBlock64`, the machine `CorresR` runs. The readout
theorem is `com_riscv_e2e`; the entry and exit relations are the machine-generic
`SRview` and `SRret` at `RState64.regs`.

`runRBlock64` is the machine of `CorresR`, so besides the `CorresMPost` form at
`runRBlock64Step` the bridge is also stated in `CorresR`'s own shape, with the
entry and exit relations spelled out.

## Main definitions

* `corres_of_refines_riscv` — the bridge at `runRBlock64Step`
* `corresR_of_refines` — the same statement in the `CorresR` shape
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.Sha2Emit
open CatCrypt.Crypto.SecureCompilation.RelationalCompile
open CatCrypt.Crypto.SecureCompilation.ScalarLin
open CatCrypt.Crypto.SecureCompilation.ScalarLinFront
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
open CatCrypt.Crypto.SecureCompilation.MultiBackendDemo
open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RegToRiscv

/-- **The RV64 bridge.** From a descent result `Refines spec frag`, the compiled
    RV64 block of the fragment closed at slot `dst` is a forward simulation at the
    abstract step `spec`: entered from a state reflecting a valuation whose readout
    is the view, it exits with the result register `comRetName` holding slot `dst`
    of `spec` applied to the view. The side conditions are those of
    `com_riscv_e2e`: the closed fragment is in the supported straight-line fragment
    (`ComOK`) and the context is all `reg 64`. -/
theorem corres_of_refines_riscv {Γ : Ctxt jasminDialect} (hΓ : AllReg64 Γ) (e : Env 64 Γ)
    {spec : StateStep 64} {frag : Frag 64} (h : Refines spec frag) (dst : Nat)
    (hok : ComOK (descentCom frag e dst)) :
    CorresMPost runRBlock64Step (SRview RState64.regs e)
      (SRret RState64.regs (comRetName (descentCom frag e dst) Γ.length) dst)
      (fun _ => True) spec
      (lowerRBlock64 (regToROp (comToRegProg (descentCom frag e dst) Γ.length))) :=
  corresMPost_of_readout runRBlock64Step RState64.regs e h dst _ _ fun V s hs =>
    ⟨_, rfl, com_riscv_e2e hok hΓ V s hs⟩

/-- The RV64 bridge in the `CorresR` shape: running the compiled block from a state
    in `SRview` lands in `SRret` at `spec` of the view. -/
theorem corresR_of_refines {Γ : Ctxt jasminDialect} (hΓ : AllReg64 Γ) (e : Env 64 Γ)
    {spec : StateStep 64} {frag : Frag 64} (h : Refines spec frag) (dst : Nat)
    (hok : ComOK (descentCom frag e dst)) :
    ∀ (s : RState64) (vw : View 64), SRview RState64.regs e s vw →
      SRret RState64.regs (comRetName (descentCom frag e dst) Γ.length) dst
        (runRBlock64 s (lowerRBlock64 (regToROp (comToRegProg (descentCom frag e dst) Γ.length))))
        (spec vw) := by
  intro s vw hin
  obtain ⟨s', hstep, hout⟩ := corres_of_refines_riscv hΓ e h dst hok s vw hin trivial
  rw [runRBlock64Step, Option.some.injEq] at hstep
  exact hstep ▸ hout

end CatCrypt.Crypto.SecureCompilation.Ascent
