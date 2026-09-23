/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanonLogicShipped

@[expose] public section

set_option autoImplicit false

/-!
# The canonicalisation renaming at the shipped kernel's register names

`MpnLoopFrontEmit.binLprog` passes `argName 0` as the accumulator register and
`[argName 1, argName 2]` as the invariant base registers, so the canonicalised
node of `mpn_and_n_loop_owned` has output register `argName 0`.
`JasminLsemExportCanonLogic.logicTau` fixes `argName 0` and `argName 1`, and its
`CanonRen` asks for `argName j ≠ out` at `j < 2`; at `out = argName 0` that is
`argName 0 ≠ argName 0`. `JasminLsemExportCanonLogic.logicTauG` carries the two
invariant base registers as parameters instead, and this module instantiates the
chain at the shipped names through it.

## Main results

* `logicSigma_comp_canonRen_slot` — the store-slot-generic form of
  `JasminLsemExportCanonLogic.logicSigma_comp_canonRen`.
* `shippedTau` — `logicTauG` at store slot `9`, output `argName 0` and invariant
  base registers `argName 2`, `argName 1`, the order
  `JasminLsemExportTransfer.LoopRen.inv` reads them off `[argName 1, argName 2]`.
* `shippedTau_canonRen` — its `CanonRen`, with no hypothesis on the names.
* `binAnd_canon_machine_shipped` — the canonicalised node of the shipped limb
  body at output register `argName 0` halts with the array there decoding to the
  source fold.
* `binAnd_canon_machine_export` — the same at `ρ ∘ logicSigma d`, the composite
  of a node renaming with the exporter's loop renaming.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportShippedRen

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanon
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanonLogic
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanonLogicShipped
open CatCrypt.Crypto.SecureCompilation.VIR.LoopNameDistinct
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddCarryFrontPrototype (N AN)

variable (d : Nat)

/-! ## 1. The composite renaming at an arbitrary store slot -/

/-- **The canonicalisation renaming composed with the loop renaming, at store
    slot `sl`.** A renaming `ρ` that sends the store slot's body temporary
    `loopReg d sl` to the output argument and fixes every other name composes
    with `logicSigma d` to a `CanonRen` at loop depth `d`, two invariants,
    store-slot set `logicS sl` and output `argName 0`. -/
theorem logicSigma_comp_canonRen_slot (sl : Nat) (ρ : String → String)
    (hρid : ∀ r, r ≠ loopReg d sl → ρ r = r) (hρs : ρ (loopReg d sl) = argName 0) :
    CanonRen (ρ ∘ logicSigma d) d 2 (logicS sl) (argName 0) :=
  canonRen_of d sl (argName 0) (argName 2) (argName 1) (ρ ∘ logicSigma d)
    (by
      show ρ (logicSigma d "") = ""
      rw [logicSigma_empty]
      exact hρid _ (fun h => absurd h.symm (ne_empty_of_head? (head?_loopReg d sl))))
    (by show ρ (logicSigma d (regName sl)) = _; rw [logicSigma_regName]; exact hρs)
    (fun k hk => by
      show ρ (logicSigma d (regName k)) = _
      rw [logicSigma_regName]
      exact hρid _ (fun h => hk (loopReg_injective d h)))
    (by
      show ρ (logicSigma d (argName 3)) = _
      rw [logicSigma_argName3]; exact hρid _ (argName_ne_loopReg d 0 sl))
    (by
      show ρ (logicSigma d (argName 2)) = _
      rw [logicSigma_argName2]; exact hρid _ (loopIdx_ne_loopReg d d sl))
    (by
      show ρ (logicSigma d (argName 1)) = _
      rw [logicSigma_argName1]; exact hρid _ (argName_ne_loopReg d 1 sl))
    (by
      show ρ (logicSigma d (argName 0)) = _
      rw [logicSigma_argName0]; exact hρid _ (argName_ne_loopReg d 2 sl))
    (by
      show ρ (logicSigma d (loopCtr d)) = _
      rw [logicSigma_loopCtr]; exact hρid _ (loopCtr_ne_loopReg d d sl))
    (argName_ne_loopReg d 0) (fun h => loopIdx_ne_argName d 0 h.symm)
    (fun h => loopCtr_ne_argName d 0 h.symm)
    (argName_ne_loopReg d 2) (argName_ne_loopReg d 1)
    (JasminLsemSimulation.argName_ne (show (2 : Nat) ≠ 0 by decide))
    (JasminLsemSimulation.argName_ne (show (1 : Nat) ≠ 0 by decide))
    (fun h => loopIdx_ne_argName d 2 h.symm) (fun h => loopIdx_ne_argName d 1 h.symm)
    (fun h => loopCtr_ne_argName d 2 h.symm) (fun h => loopCtr_ne_argName d 1 h.symm)

/-! ## 2. The shipped kernel's renaming -/

/-- The canonicalisation renaming of the shipped `mpn_and_n_loop_owned` chain:
    `logicTauG` at store slot `9`, output register `argName 0` and invariant base
    registers `argName 2` and `argName 1`. -/
noncomputable def shippedTau : String → String :=
  logicTauG d 9 (argName 0) (argName 2) (argName 1)

/-- `shippedTau d` is a `CanonRen` at loop depth `d`, two invariants and the
    store-slot set `logicS 9`, with output register `argName 0`. -/
theorem shippedTau_canonRen : CanonRen (shippedTau d) d 2 (logicS 9) (argName 0) :=
  logicTauG_canonRen d 9 (argName 0) (argName 2) (argName 1)
    (argName_ne_loopReg d 0) (fun h => loopIdx_ne_argName d 0 h.symm)
    (fun h => loopCtr_ne_argName d 0 h.symm)
    (argName_ne_loopReg d 2) (argName_ne_loopReg d 1)
    (JasminLsemSimulation.argName_ne (show (2 : Nat) ≠ 0 by decide))
    (JasminLsemSimulation.argName_ne (show (1 : Nat) ≠ 0 by decide))
    (fun h => loopIdx_ne_argName d 2 h.symm) (fun h => loopIdx_ne_argName d 1 h.symm)
    (fun h => loopCtr_ne_argName d 2 h.symm) (fun h => loopCtr_ne_argName d 1 h.symm)

theorem shippedTau_argName0 : shippedTau d (argName 0) = argName 2 :=
  logicTauG_argName0 d 9 (argName 0) (argName 2) (argName 1)

theorem shippedTau_argName1 : shippedTau d (argName 1) = argName 1 :=
  logicTauG_argName1 d 9 (argName 0) (argName 2) (argName 1)

/-! ## 3. The chain at the shipped output register -/

/-- **The canonicalised shipped `mpn_and_n_loop_owned` node computes the model
    loop, at the output register the exporter gives it.** The canonicalised,
    aliased export loop node of the shipped limb body, renamed by `shippedTau d`
    and run on the flag machine from program counter `0` with the seed
    agreement, readable invariant base registers and the trip count in `c`,
    halts with the array at `argName 0` decoding to the source fold of that
    body. -/
theorem binAnd_canon_machine_shipped
    (absent : Bool) (regs : List String)
    (hregs : ∀ r ∈ regs, ∃ j, j < ([AN, AN] : Ctxt jasminDialect).length ∧
      r = shippedTau d (argName j))
    (invs : Ctxt.Valuation ([AN, AN] : Ctxt jasminDialect))
    (fn c : String) (hc : c ≠ loopIdx d)
    (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0) (arr0 : Fin N → BitVec 64)
    (hseed : StoreAgreesM (([AN, AN] : Ctxt jasminDialect).length + 2)
      (([AN, AN] : Ctxt jasminDialect).length + 2)
      (pullM (shippedTau d) (b0.setReg (loopIdx d) (0#64)))
      (tripValArrMN invs 0 arr0))
    (hinv : ∀ j, j < ([AN, AN] : Ctxt jasminDialect).length →
      (b0.reg.getW (shippedTau d (argName j)) 64).isSome)
    (m : Nat) (hm64 : m < 2 ^ 64)
    (hcnt : b0.reg.getW c 64 = some (BitVec.ofNat 64 m)) :
    ∃ (k : Nat) (t : LstateMF),
      lsemFuelMemF (singletonProgM fn
          (canonNodeRM (shippedTau d) d (argName 0) c binAndUpdate absent regs)) k
          { prog := { base := b0, lfn := fn }, zf := zf } = some t
        ∧ decodeArrM t.prog.base (argName 0) 64 N
            = some (JLoopBodyN.denote ⟨m, binAndUpdate⟩ invs arr0) :=
  binAnd_canon_machine_denoteT d (argName 0) (shippedTau d) (shippedTau_canonRen d)
    (by
      rw [shippedTau_argName0]
      exact JasminLsemSimulation.argName_ne (show (2 : Nat) ≠ 0 by decide))
    (by
      rw [shippedTau_argName1]
      exact JasminLsemSimulation.argName_ne (show (1 : Nat) ≠ 0 by decide))
    absent regs hregs invs fn c hc b0 zf hpc arr0 hseed hinv m hm64 hcnt

/-- **The same at the composite of a node renaming with the exporter's loop
    renaming.** `logicSigma d` is the exporter's `LoopRen` at accumulator
    register `argName 0` and invariant base registers `[argName 1, argName 2]`
    (`JasminLsemExportCanonLogic.logicSigma_loopRen`), the arguments
    `MpnLoopFrontEmit.binLprog` passes; `ρ` is the node renaming that sends the
    store slot's body temporary to `argName 0`. -/
theorem binAnd_canon_machine_export (ρ : String → String)
    (hρid : ∀ r, r ≠ loopReg d 9 → ρ r = r) (hρs : ρ (loopReg d 9) = argName 0)
    (absent : Bool) (regs : List String)
    (hregs : ∀ r ∈ regs, ∃ j, j < ([AN, AN] : Ctxt jasminDialect).length ∧
      r = (ρ ∘ logicSigma d) (argName j))
    (invs : Ctxt.Valuation ([AN, AN] : Ctxt jasminDialect))
    (fn c : String) (hc : c ≠ loopIdx d)
    (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0) (arr0 : Fin N → BitVec 64)
    (hseed : StoreAgreesM (([AN, AN] : Ctxt jasminDialect).length + 2)
      (([AN, AN] : Ctxt jasminDialect).length + 2)
      (pullM (ρ ∘ logicSigma d) (b0.setReg (loopIdx d) (0#64)))
      (tripValArrMN invs 0 arr0))
    (hinv : ∀ j, j < ([AN, AN] : Ctxt jasminDialect).length →
      (b0.reg.getW ((ρ ∘ logicSigma d) (argName j)) 64).isSome)
    (m : Nat) (hm64 : m < 2 ^ 64)
    (hcnt : b0.reg.getW c 64 = some (BitVec.ofNat 64 m)) :
    ∃ (k : Nat) (t : LstateMF),
      lsemFuelMemF (singletonProgM fn
          (canonNodeRM (ρ ∘ logicSigma d) d (argName 0) c binAndUpdate absent regs)) k
          { prog := { base := b0, lfn := fn }, zf := zf } = some t
        ∧ decodeArrM t.prog.base (argName 0) 64 N
            = some (JLoopBodyN.denote ⟨m, binAndUpdate⟩ invs arr0) :=
  binAnd_canon_machine_denoteT d (argName 0) (ρ ∘ logicSigma d)
    (logicSigma_comp_canonRen_slot d 9 ρ hρid hρs)
    (by
      show ρ (logicSigma d (argName 0)) ≠ _
      rw [logicSigma_argName0, hρid _ (argName_ne_loopReg d 2 9)]
      exact JasminLsemSimulation.argName_ne (show (2 : Nat) ≠ 0 by decide))
    (by
      show ρ (logicSigma d (argName 1)) ≠ _
      rw [logicSigma_argName1, hρid _ (argName_ne_loopReg d 1 9)]
      exact JasminLsemSimulation.argName_ne (show (1 : Nat) ≠ 0 by decide))
    absent regs hregs invs fn c hc b0 zf hpc arr0 hseed hinv m hm64 hcnt

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportShippedRen
