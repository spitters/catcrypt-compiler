/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSrc

@[expose] public section

set_option autoImplicit false

/-!
# The virtual body of the register allocation check at an explicit fuel

`ImageAddrSrc.src_chain` and `ImageAddrSrc.src_chain_fuse` match a halting run of the
exported node `seeds ++ loop` at fuel `fuel` by a halting run of the virtual body at some
fuel. The moves `pre0` in front cost their length, the copies `movesOf ps` cost one step per
pair, and the renamed loop runs step for step, so the virtual body halts at fuel
`pre0.length + fuel + ps.length`; the fusion of the renamed loop multiplies that fuel by at
most four. Both results at those fuels (`src_chain_fuel`, `src_chain_fuse_fuel`, with the
fuels `srcFuel` and `srcFuseFuel`), in the form "the virtual body halts in one state at every
fuel from the bound on", are in the module `ImageAddrSrc`, in this namespace. This module
derives the statements of `ImageAddrSrc` from them.

## Main results

* `src_chain_of_fuel`, `src_chain_fuse_of_fuel`: the statements of `ImageAddrSrc.src_chain`
  and `ImageAddrSrc.src_chain_fuse`, from the forms at an explicit fuel.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSrcFuel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLower
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagPrefix
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSrc
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa x86Isa_lsemFuelMemF)

/-- The statement of `ImageAddrSrc.src_chain`, from `src_chain_fuel` at the fuel
    `srcFuel pre0.length ps.length fuel`. -/
theorem src_chain_of_fuel (fn : String) (pre0 seeds loop : List LinstrRM)
    (ps : List (String × String))
    (N : String → Prop) (hpre0 : ∀ i ∈ pre0, IsLopn i) (hseeds : ∀ i ∈ seeds, IsLopn i)
    (hloop : ∀ i ∈ loop, CtlOK i) (hcond : ∀ i ∈ loop, CondOK i) (hσ : RenOn (renOf ps) N)
    (hn : ∀ i ∈ loop, ∀ n ∈ instrNames i.1, N n) (hnd : (ps.map Prod.snd).Nodup)
    (hts : ∀ p ∈ ps, ∀ q ∈ ps, q.2 ≠ p.1) (hren : ∀ p ∈ ps, renOf ps p.1 = p.2)
    (hfresh : ∀ p ∈ ps, ¬ N p.2) (b0 b1 : LstateM) (zf : Bool) (h0 : b0.lpc = 0)
    (hpr : runStraightF pre0 b0 zf = some (b1, zf)) (hb1 : b1.setLpc 0 = b0)
    (hA : ∀ b2 z2, runStraightF (pre0 ++ seeds) b0 zf = some (b2, z2) →
      ∀ r, N r → b2.larr (renOf ps r) = b2.larr r)
    (fuel : Nat) (t : LstateMF)
    (hrun : lsemFuelMemF (singletonProgM fn (seeds ++ loop)) fuel
      { prog := { base := b0, lfn := fn }, zf := zf } = some t)
    (out : String) (hout : N out) (w n : Nat) :
    ∃ fuel' t', lsemFuelMemF
        (singletonProgM fn (pre0 ++ seeds ++ movesOf ps ++ loop.map (renRM (renOf ps))))
        fuel' { prog := { base := b0, lfn := fn }, zf := zf } = some t'
      ∧ t'.prog.base.getArr (renOf ps out) w n = t.prog.base.getArr out w n := by
  obtain ⟨t', hk, harr⟩ := src_chain_fuel fn pre0 seeds loop ps N hpre0 hseeds hloop hcond hσ
    hn hnd hts hren hfresh b0 b1 zf h0 hpr hb1 hA fuel t hrun out hout w n
  exact ⟨_, t', hk _ (Nat.le_refl _), harr⟩

/-- The statement of `ImageAddrSrc.src_chain_fuse`, from `src_chain_fuse_fuel` at the fuel
    `srcFuseFuel pre0.length ps.length fuel`. -/
theorem src_chain_fuse_of_fuel (fn : String) (pre0 seeds loop : List LinstrRM)
    (ps : List (String × String)) (N : String → Prop) (hpre0 : ∀ i ∈ pre0, IsLopn i)
    (hseeds : ∀ i ∈ seeds, IsLopn i)
    (hloop : ∀ i ∈ loop, CtlOK i) (hcond : ∀ i ∈ loop, CondOK i) (hσ : RenOn (renOf ps) N)
    (hn : ∀ i ∈ loop, ∀ n ∈ instrNames i.1, N n) (hnd : (ps.map Prod.snd).Nodup)
    (hts : ∀ p ∈ ps, ∀ q ∈ ps, q.2 ≠ p.1) (hren : ∀ p ∈ ps, renOf ps p.1 = p.2)
    (hfresh : ∀ p ∈ ps, ¬ N p.2) (b0 b1 : LstateM) (zf : Bool) (h0 : b0.lpc = 0)
    (hpr : runStraightF pre0 b0 zf = some (b1, zf)) (hb1 : b1.setLpc 0 = b0)
    (hA : ∀ b2 z2, runStraightF (pre0 ++ seeds) b0 zf = some (b2, z2) →
      ∀ r, N r → b2.larr (renOf ps r) = b2.larr r)
    {E : List String}
    (hfuse : fuseOKL E (fuseLoPre (pre0 ++ seeds ++ movesOf ps) (loop.map (renRM (renOf ps))))
      (pre0 ++ seeds ++ movesOf ps ++ loop.map (renRM (renOf ps))) = true)
    (hE : E64 E b0)
    (fuel : Nat) (t : LstateMF)
    (hrun : lsemFuelMemF (singletonProgM fn (seeds ++ loop)) fuel
      { prog := { base := b0, lfn := fn }, zf := zf } = some t)
    (out : String) (hout : N out) (hkept : KeptN (renOf ps out)) (w n : Nat) :
    ∃ fuel' t', lsemFuelMemF
        (singletonProgM fn (pre0 ++ seeds ++ movesOf ps
          ++ fuseMulHiRM (loop.map (renRM (renOf ps)))))
        fuel' { prog := { base := b0, lfn := fn }, zf := zf } = some t'
      ∧ t'.prog.base.getArr (renOf ps out) w n = t.prog.base.getArr out w n := by
  obtain ⟨t', hk, harr⟩ := src_chain_fuse_fuel fn pre0 seeds loop ps N hpre0 hseeds hloop
    hcond hσ hn hnd hts hren hfresh b0 b1 zf h0 hpr hb1 hA hfuse hE fuel t hrun out hout
    hkept w n
  exact ⟨_, t', hk _ (Nat.le_refl _), harr⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSrcFuel
