/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanonLogic
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportChain

/-!
# The logic kernels through the export passes

`JasminLsemExportCanonLogic` states what the canonicalised aliased loop node of
the `and`, `ior` and `xor` kernels computes: the cells at the accumulator name
are the elementwise operation of the two source arrays.
`JasminLsemExportChain.alloc_lower_decodeArrM` carries a halting run of a body
through the register table and the two-address lowering, reading the array of a
live name at that name's image.

Composing the two gives the elementwise conclusion on the allocated and lowered
body: the array the register table assigns to the accumulator holds the
elementwise operation.
-/

public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportChainLogic

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLower
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanon
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanonLogic
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportChain
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit (cells)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalFrontEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalFrontDenote

/-- **The and kernel through canonicalisation, allocation and lowering.** The
    canonicalised aliased node of the `and` kernel, allocated by a register table
    `σ` meeting the range certificates and then two-address lowered, halts with
    the array at `σ out` decoding to a value whose first `n` cells are the
    elementwise conjunction of the two source arrays.

    The canonicalisation hypotheses are those of `and_canon_machine_val`, the
    allocation hypotheses those of `lsemFuelMemF_ranges` and the lowering
    hypotheses those of `lsemFuelMemF_lowerRM`, at the node as body. -/
theorem and_chain_machine_val {d : Nat} {out : String} {σ : String → String}
    {rr ra : String → Nat × Nat} {InR InA : String → Prop}
    {isB : String → Bool} {movFor : String → String}
    (V : Ctxt.Valuation Gouter) (hn : (logicCount.lookup V).toNat ≤ NL)
    (hoR : ∀ k, out ≠ loopReg d k) (hoI : out ≠ loopIdx d) (hoC : out ≠ loopCtr d)
    (hoA : ∀ j, j < 2 → argName j ≠ out)
    (absent : Bool) (regs : List String)
    (hregs : ∀ r ∈ regs, ∃ j, j < ([AL, AL] : Ctxt jasminDialect).length ∧
      r = logicTau d 8 out (argName j))
    (fn c : String) (hc : c ≠ loopIdx d)
    (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0)
    (hseed : StoreAgreesM (([AL, AL] : Ctxt jasminDialect).length + 2)
      (([AL, AL] : Ctxt jasminDialect).length + 2)
      (pullM (logicTau d 8 out) (b0.setReg (loopIdx d) (0#64)))
      (tripValArrMN (Expr.lookupArgs logicInvs V) 0 (logicInit.lookup V)))
    (hinv : ∀ j, j < ([AL, AL] : Ctxt jasminDialect).length →
      (b0.reg.getW (logicTau d 8 out (argName j)) 64).isSome)
    (hm64 : (logicCount.lookup V).toNat < 2 ^ 64)
    (hcnt : b0.reg.getW c 64 = some (BitVec.ofNat 64 (logicCount.lookup V).toNat))
    (k0 : Nat) (hfix : σ "" = "") (hne : ∀ n, n ≠ "" → σ n ≠ "")
    (hcond : ∀ k i, k0 ≤ k →
      (canonNodeRM (logicTau d 8 out) d out c andUpdate absent regs)[k]? = some i → CondOK i)
    (hjmp : ∀ l pc,
      findLabelMem l (canonNodeRM (logicTau d 8 out) d out c andUpdate absent regs)
        = some pc → k0 ≤ pc + 1)
    (hR : RangeCert σ k0 (canonNodeRM (logicTau d 8 out) d out c andUpdate absent regs)
      regDefs rr InR)
    (hA : RangeCert σ k0 (canonNodeRM (logicTau d 8 out) d out c andUpdate absent regs)
      arrDefs ra InA)
    (huse : ∀ k i, k0 ≤ k →
      (canonNodeRM (logicTau d 8 out) d out c andUpdate absent regs)[k]? = some i →
        ∀ n ∈ useNames i.1, Live rr InR k n)
    (harr : ∀ k i, k0 ≤ k →
      (canonNodeRM (logicTau d 8 out) d out c andUpdate absent regs)[k]? = some i →
        ∀ b, arrUse? i = some b → Live ra InA k b)
    (hjR : JumpOK (canonNodeRM (logicTau d 8 out) d out c andUpdate absent regs) k0 rr InR)
    (hjA : JumpOK (canonNodeRM (logicTau d 8 out) d out c andUpdate absent regs) k0 ra InA)
    (hlow : LowerOK isB movFor (singletonProgM fn
      ((canonNodeRM (logicTau d 8 out) d out c andUpdate absent regs).map (renRM σ))))
    (s' s'' : LstateMF)
    (hrel : RelF2 σ (Live rr InR 0) (Live ra InA 0)
      { prog := { base := b0, lfn := fn }, zf := zf } s')
    (hk : k0 ≤ 0)
    (hrelX : RelX EqPc (lowerRM isB movFor) (singletonProgM fn
      ((canonNodeRM (logicTau d 8 out) d out c andUpdate absent regs).map (renRM σ))) s' s'')
    (hlive : ∀ pc, Live ra InA pc out) :
    ∃ (fuel : Nat) (t : LstateMF) (o : Fin NL → BitVec 64),
      lsemFuelMemF
          ⟨fn, ((canonNodeRM (logicTau d 8 out) d out c andUpdate absent regs).map (renRM σ)).flatMap
            (lowerRM isB movFor)⟩ fuel s'' = some t
        ∧ decodeArrM t.prog.base (σ out) 64 NL = some o
        ∧ cells o (logicCount.lookup V).toNat
            = List.zipWith (fun x y => x &&& y)
                (cells (apVar.lookup V) (logicCount.lookup V).toNat)
                (cells (bpVar.lookup V) (logicCount.lookup V).toNat) := by
  obtain ⟨k, t, o, hrun, hdec, hcells⟩ :=
    and_canon_machine_val (d := d) (out := out) V hn hoR hoI hoC hoA absent regs hregs
      fn c hc b0 zf hpc hseed hinv hm64 hcnt
  have hpc0 : ({ prog := { base := b0, lfn := fn }, zf := zf } :
      LstateMF).prog.base.lpc = 0 := hpc
  obtain ⟨fuel, t', hrunl, hdecl⟩ :=
    alloc_lower_decodeArrM (σ := σ) fn
      (canonNodeRM (logicTau d 8 out) d out c andUpdate absent regs) k0 hfix hne hcond hjmp
      hR hA huse harr hjR hjA hlow k (hpc0 ▸ hrel) (hpc0 ▸ hk) hrelX hrun out 64 NL
      (hlive _)
  exact ⟨fuel, t', o, hrunl, hdecl.trans hdec, hcells⟩

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportChainLogic
