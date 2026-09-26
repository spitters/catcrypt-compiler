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
elementwise operation. The array liveness of the accumulator is asked at the
program counters of the body only, because a halting flag-machine run started
inside the body ends at or before its end (`lsemFuelMemF_lpc_le`).

## Main results

* `lsemFuelMemF_lpc_le` — the halting program counter of a flag-machine run is
  at most the body length.
* `and_chain_machine_val` — the and kernel through canonicalisation, allocation
  and lowering.
-/

public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportChainLogic

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledMC
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
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

/-! ## The halting program counter of a run -/

/-- A successful cast-aware step advances the program counter by one. -/
theorem lsemStepCast_lpc_succ (i : LinstrRT) (s s' : LstateN) (h : lsemStepCast i s = some s') :
    s'.lpc = s.lpc + 1 := by
  unfold lsemStepCast at h
  repeat' split at h
  all_goals
    first
      | (obtain rfl := Option.some.inj h; simp)
      | exact lsemStepMC_lpc_succ _ s s' h
      | simp at h

/-- A successful memory step advances the program counter by one. -/
theorem lsemStepMem_lpc_succ (i : LinstrRM) (s s' : LstateM) (h : lsemStepMem i s = some s') :
    s'.lpc = s.lpc + 1 := by
  unfold lsemStepMem at h
  repeat' split at h
  all_goals
    first
      | (obtain rfl := Option.some.inj h; simp; done)
      | (obtain rfl := Option.some.inj h; simp; rfl)
      | (rw [Option.map_eq_some_iff] at h
         obtain ⟨r, hr, rfl⟩ := h
         exact lsemStepCast_lpc_succ _ _ _ hr)
      | simp at h

/-- A resolved jump lands inside the body. -/
theorem evalJumpMem_lpc_le (P : LprogM) (lbl : LLabel) (p p' : LstatePM)
    (h : evalJumpMem P lbl p = some p') : p'.base.lpc ≤ P.body.length := by
  unfold evalJumpMem at h
  split at h
  · rename_i pc hpc
    obtain rfl := Option.some.inj h
    have := findLabel_lt_length lbl (P.body.map Prod.fst) pc hpc
    simp only [List.length_map] at this
    simp
    omega
  · simp at h

/-- A step of the control-transfer arm from inside the body ends at or before its
    end. -/
theorem evalInstrPMemL_lpc_le (P : LprogM) (i : LinstrRM) (p p' : LstatePM)
    (hs : p.base.lpc < P.body.length) (h : evalInstrPMemL P i p = some p') :
    p'.base.lpc ≤ P.body.length := by
  unfold evalInstrPMemL at h
  repeat' split at h
  all_goals
    first
      | (obtain rfl := Option.some.inj h; simp; omega)
      | exact evalJumpMem_lpc_le P _ _ _ h
      | (rw [Option.map_eq_some_iff] at h
         obtain ⟨b, hb, rfl⟩ := h
         have := lsemStepMem_lpc_succ _ _ _ hb
         show b.lpc ≤ _
         omega)
      | simp at h

/-- A flag-machine step from inside the body ends at or before its end. -/
theorem evalInstrPMemF_lpc_le (P : LprogM) (i : LinstrRM) (s t : LstateMF)
    (hs : s.prog.base.lpc < P.body.length) (h : evalInstrPMemF P i s = some t) :
    t.prog.base.lpc ≤ P.body.length := by
  unfold evalInstrPMemF at h
  repeat' split at h
  all_goals
    first
      | (obtain rfl := Option.some.inj h; simp; omega)
      | (rw [Option.map_eq_some_iff] at h
         obtain ⟨p, hp, rfl⟩ := h
         first
           | exact evalJumpMem_lpc_le P _ _ _ hp
           | exact evalInstrPMemL_lpc_le P i _ _ hs hp)
      | simp at h

/-- **The halting program counter of a flag-machine run** lies at or before the end
    of the body, when the run starts there. -/
theorem lsemFuelMemF_lpc_le (P : LprogM) (fuel : Nat) (s t : LstateMF)
    (hs : s.prog.base.lpc ≤ P.body.length) (h : lsemFuelMemF P fuel s = some t) :
    t.prog.base.lpc ≤ P.body.length := by
  induction fuel generalizing s with
  | zero =>
      unfold lsemFuelMemF at h
      split at h
      · obtain rfl := Option.some.inj h; exact hs
      · simp at h
  | succ n ih =>
      unfold lsemFuelMemF at h
      split at h
      · obtain rfl := Option.some.inj h; exact hs
      · rename_i i hi
        split at h
        · rename_i s' hs'
          have hlt : s.prog.base.lpc < P.body.length := by
            unfold findInstrMem at hi
            split at hi
            · exact (List.getElem?_eq_some_iff.mp hi).1
            · simp at hi
          exact ih s' (evalInstrPMemF_lpc_le P i s s' hlt hs') h
        · simp at h

/-! ## The and kernel through the passes -/

/-- **The and kernel through canonicalisation, allocation and lowering.** The
    canonicalised aliased node of the `and` kernel, allocated by a register table
    `σ` meeting the range certificates and then two-address lowered, halts with
    the array at `σ out` decoding to a value whose first `n` cells are the
    elementwise conjunction of the two source arrays.

    The canonicalisation hypotheses are those of `and_canon_machine_val`, the
    allocation hypotheses those of `lsemFuelMemF_ranges` and the lowering
    hypotheses those of `lsemFuelMemF_lowerRM`, at the node as body. The array
    liveness of `out` is asked at the program counters of the body. -/
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
    (hlive : ∀ pc, pc ≤ (canonNodeRM (logicTau d 8 out) d out c andUpdate absent regs).length →
      Live ra InA pc out) :
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
  have hend : t.prog.base.lpc
      ≤ (canonNodeRM (logicTau d 8 out) d out c andUpdate absent regs).length :=
    lsemFuelMemF_lpc_le _ k _ t (by rw [hpc0]; exact Nat.zero_le _) hrun
  obtain ⟨fuel, t', hrunl, hdecl⟩ :=
    alloc_lower_decodeArrM (σ := σ) fn
      (canonNodeRM (logicTau d 8 out) d out c andUpdate absent regs) k0 hfix hne hcond hjmp
      hR hA huse harr hjR hjA hlow k (hpc0 ▸ hrel) (hpc0 ▸ hk) hrelX hrun out 64 NL
      (hlive _ hend)
  exact ⟨fuel, t', o, hrunl, hdecl.trans hdec, hcells⟩

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportChainLogic
