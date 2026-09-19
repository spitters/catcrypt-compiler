/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanon
public import CatCrypt.Crypto.SecureCompilation.VIR.LoopNameDistinct

@[expose] public section

set_option autoImplicit false

/-!
# The canonicalised export loop node of the elementwise logical kernels

`JasminLsemExportCanon.canonNodeRM_faithful` states that the canonicalised,
aliased export loop node halts with the array at `out` equal to the source fold
`JLoopBodyN.denote`, under a renaming certificate `CanonRen` and a thread
certificate `ThreadCert`. This module supplies both for the `mpn_and_n`,
`mpn_ior_n` and `mpn_xor_n` limb bodies and composes the result with
`MpnLogicalFrontEmit.andFold_cells` and its siblings.

## Contents

* **§1** `logicTau`, `logicS`, `logicTau_canonRen`: the renaming from the model
  chain's names to the canonicalised node's names, and its `CanonRen`
  certificate.
* **§2** `andUpdate_threadCert`, `iorUpdate_threadCert`, `xorUpdate_threadCert`:
  the thread certificates of the three chains.
* **§3** `and_canon_machine_val`, `ior_canon_machine_val`,
  `xor_canon_machine_val`: the canonicalised node of each kernel halts with the
  cells at `out` the elementwise operation on the two source arrays.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanonLogic

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanon
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemArrTripLogical
open CatCrypt.Crypto.SecureCompilation.VIR.LoopNameDistinct
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit (cells)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalFrontEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalFrontDenote
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalLsemTie

/-! ## 1. The renaming of the logic family's chain names -/

/-- The chain slots of a logic body that hold a store: the slot `sl`, the one
    that writes the output array. -/
def logicS (sl : Nat) : Nat → Prop := fun k => k = sl

attribute [local instance] Classical.propDecidable

/-- The renaming from the model chain's names to the names of the canonicalised
    export node at loop depth `d` with output register `out` and store slot `sl`:
    the accumulator argument and the store slot go to `out`, the index argument
    to the loop index, every other chain register to its body temporary, every
    other name to itself. -/
noncomputable def logicTau (d sl : Nat) (out : String) (r : String) : String :=
  if r = argName 3 then out
  else if r = argName 2 then loopIdx d
  else if r = regName sl then out
  else if h : ∃ k, r = regName k then loopReg d h.choose
  else r

variable (d sl : Nat) (out : String)

theorem logicTau_argName3 : logicTau d sl out (argName 3) = out := by
  simp [logicTau]

theorem logicTau_argName2 : logicTau d sl out (argName 2) = loopIdx d := by
  simp [logicTau, JasminLsemSimulation.argName_ne (show (2 : Nat) ≠ 3 by decide)]

theorem logicTau_regName_store : logicTau d sl out (regName sl) = out := by
  simp [logicTau, JasminLsemSimulation.regName_ne_argName]

theorem logicTau_regName {k : Nat} (hk : k ≠ sl) :
    logicTau d sl out (regName k) = loopReg d k := by
  have h7 : regName k ≠ regName sl := fun h => hk (JasminLsemSimulation.regName_injective h)
  have hex : ∃ k', regName k = regName k' := ⟨k, rfl⟩
  rw [logicTau, if_neg (JasminLsemSimulation.regName_ne_argName k 3),
    if_neg (JasminLsemSimulation.regName_ne_argName k 2), if_neg h7, dif_pos hex,
    JasminLsemSimulation.regName_injective hex.choose_spec.symm]

theorem logicTau_other {r : String} (h1 : r ≠ argName 3) (h2 : r ≠ argName 2)
    (h3 : ∀ k, r ≠ regName k) : logicTau d sl out r = r := by
  rw [logicTau, if_neg h1, if_neg h2, if_neg (h3 sl), dif_neg]
  rintro ⟨k, rfl⟩
  exact h3 k rfl

/-- The argument names other than the accumulator and the index are fixed. -/
theorem logicTau_argName_lt {j : Nat} (hj : j < 2) :
    logicTau d sl out (argName j) = argName j :=
  logicTau_other d sl out (JasminLsemSimulation.argName_ne (by omega))
    (JasminLsemSimulation.argName_ne (by omega))
    (fun k h => JasminLsemSimulation.regName_ne_argName k j h.symm)

theorem logicTau_loopCtr : logicTau d sl out (loopCtr d) = loopCtr d :=
  logicTau_other d sl out (loopCtr_ne_argName d 3) (loopCtr_ne_argName d 2)
    (loopCtr_ne_regName d)

theorem logicTau_empty : logicTau d sl out "" = "" :=
  logicTau_other d sl out (fun h => absurd h.symm (ne_empty_of_head? (head?_argName 3)))
    (fun h => absurd h.symm (ne_empty_of_head? (head?_argName 2)))
    (fun k h => absurd h.symm (ne_empty_of_head? (head?_regName k)))

/-- A loop index `Lidx<d>` starts with `L`. -/
theorem head?_loopIdx : (loopIdx d).toList.head? = some 'L' :=
  head?_append_of _ _ _ rfl

/-- A loop index is no argument register. -/
theorem loopIdx_ne_argName (j : Nat) : loopIdx d ≠ argName j :=
  ne_of_head? _ _ _ _ (head?_loopIdx d) (head?_argName j) (by decide)

/-- An argument register is no body temporary. -/
theorem argName_ne_loopReg (j k : Nat) : argName j ≠ loopReg d k :=
  ne_of_head? _ _ _ _ (head?_argName j) (head?_loopReg d k) (by decide)

/-- **The logic family's renaming certificate.** `logicTau d sl out` satisfies
    `CanonRen` at loop depth `d`, two invariants and the store-slot set
    `logicS sl`, whenever `out` is distinct from the loop index, the trip
    counter, every body temporary and the two invariant argument registers. -/
theorem logicTau_canonRen
    (hoR : ∀ k, out ≠ loopReg d k) (hoI : out ≠ loopIdx d) (hoC : out ≠ loopCtr d)
    (hoA : ∀ j, j < 2 → argName j ≠ out) :
    CanonRen (logicTau d sl out) d 2 (logicS sl) out where
  fix := logicTau_empty d sl out
  tmp := by
    intro k _ hS
    exact logicTau_regName d sl out (fun h => hS h)
  thr := by
    intro k _ hS
    have hk : k = sl := hS
    subst hk
    exact logicTau_regName_store d k out
  arg := by
    intro j k hj
    interval_cases j
    · rw [logicTau_argName_lt d sl out (by omega)]; exact argName_ne_loopReg d 0 k
    · rw [logicTau_argName_lt d sl out (by omega)]; exact argName_ne_loopReg d 1 k
    · rw [logicTau_argName2]; exact loopIdx_ne_loopReg d d k
    · rw [logicTau_argName3]; exact hoR k
  outL := hoR
  acc := logicTau_argName3 d sl out
  idx := logicTau_argName2 d sl out
  ctr := logicTau_loopCtr d sl out
  argOut := by
    intro j hj
    interval_cases j
    · rw [logicTau_argName_lt d sl out (by omega)]; exact hoA 0 (by omega)
    · rw [logicTau_argName_lt d sl out (by omega)]; exact hoA 1 (by omega)
    · rw [logicTau_argName2]; exact fun h => hoI h.symm
  invIdx := by
    intro j hj
    rw [logicTau_argName_lt d sl out hj]
    exact fun h => loopIdx_ne_argName d j h.symm
  invCtr := by
    intro j hj
    rw [logicTau_argName_lt d sl out hj]
    exact fun h => loopCtr_ne_argName d j h.symm
  outIdx := hoI
  outCtr := hoC
  idxCtr := loopIdx_ne_loopCtr d
  ctrL := loopCtr_ne_loopReg d d

/-! ## 2. The thread certificates of the three chains -/

/-- An argument name is resolved. -/
theorem resolved_argName {nArgs cd j : Nat} (h : j < nArgs) :
    Resolved nArgs cd (argName j) := Or.inr (Or.inl ⟨j, h, rfl⟩)

/-- An earlier chain register is resolved. -/
theorem resolved_regName {nArgs cd k : Nat} (h1 : nArgs ≤ k) (h2 : k < cd) :
    Resolved nArgs cd (regName k) := Or.inr (Or.inr ⟨k, h1, h2, rfl⟩)

/-- A load's two argument operands are resolved. -/
theorem threadUses_args (j j' cd : Nat) (hj : j < 4 ∧ j' < 4) :
    ∀ n ∈ [argName j, argName j'], Resolved 4 cd n := by
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact resolved_argName hj.1
  · exact resolved_argName hj.2

/-- A binary operation's two chain operands are resolved. -/
theorem threadUses_regs (k k' cd : Nat) (hk : 4 ≤ k ∧ k < cd) (hk' : 4 ≤ k' ∧ k' < cd) :
    ∀ n ∈ [regName k, regName k'], Resolved 4 cd n := by
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact resolved_regName hk.1 hk.2
  · exact resolved_regName hk'.1 hk'.2

/-- A unary operation's chain operand is resolved. -/
theorem threadUses_reg (k cd : Nat) (hk : 4 ≤ k ∧ k < cd) :
    ∀ n ∈ [regName k], Resolved 4 cd n := by
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  subst hn
  exact resolved_regName hk.1 hk.2

/-- A store's operands — the accumulator argument, the loop index argument and
    the stored chain register — are resolved. -/
theorem threadUses_store (k cd : Nat) (hk : 4 ≤ k ∧ k < cd) :
    ∀ n ∈ [argName 3, argName 2, regName k], Resolved 4 cd n := by
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl
  · exact resolved_argName (by omega)
  · exact resolved_argName (by omega)
  · exact resolved_regName hk.1 hk.2

/-- A load through an invariant array argument passes the array-use condition:
    that argument's image is not `out`. -/
theorem threadArr_inv (j : Nat) (hj : j < 2) (hoA : ∀ j, j < 2 → argName j ≠ out) :
    ∀ b, some (argName j) = some b → logicTau d sl out b = out → b = argName 3 := by
  intro b hb hbo
  cases hb
  rw [logicTau_argName_lt d sl out hj] at hbo
  exact absurd hbo (hoA j hj)

/-- An instruction that touches no array passes the array-use condition. -/
theorem threadArr_none :
    ∀ b, (none : Option String) = some b → logicTau d sl out b = out → b = argName 3 := by
  intro b hb
  simp at hb

/-- A store through the accumulator argument passes the array-use condition: that
    argument is the thread head. -/
theorem threadArr_acc :
    ∀ b, some (argName 3) = some b → logicTau d sl out b = out → b = argName 3 := by
  intro b hb _
  cases hb
  rfl

/-- **The thread certificate of the `mpn_and_n` chain.** The chain loads the two
    source limbs from the invariant arrays, combines them, and stores the result
    through the accumulator argument, so its only store result is its last slot
    and the accumulator thread head never moves before it. -/
theorem andUpdate_threadCert (hoA : ∀ j, j < 2 → argName j ≠ out) :
    ThreadCert (logicTau d 8 out) (([AL, AL] : Ctxt jasminDialect).length + 2)
      (logicS 8) out
      (straightOpsMem (([AL, AL] : Ctxt jasminDialect).length + 2) andUpdate
        (([AL, AL] : Ctxt jasminDialect).length + 2))
      (([AL, AL] : Ctxt jasminDialect).length + 2)
      (accRegMN [AL, AL]) (loopBodyRetArrMN andUpdate) := by
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [logicS], ?_⟩⟩
  · exact threadUses_args 1 2 4 (by omega)
  · exact threadArr_inv d 8 out 1 (by omega) hoA
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [logicS], ?_⟩⟩
  · exact threadUses_args 0 2 5 (by omega)
  · exact threadArr_inv d 8 out 0 (by omega) hoA
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [logicS], ?_⟩⟩
  · exact threadUses_regs 4 5 6 (by omega) (by omega)
  · exact threadArr_none d 8 out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [logicS], ?_⟩⟩
  · exact threadUses_reg 6 7 (by omega)
  · exact threadArr_none d 8 out
  refine ⟨?_, ?_, Or.inr ⟨rfl, rfl, rfl⟩⟩
  · exact threadUses_store 7 8 (by omega)
  · exact threadArr_acc d 8 out

/-- **The thread certificate of the `mpn_xor_n` chain.** The exclusive-or chain
    has the shape of the conjunction chain, the combining instruction aside. -/
theorem xorUpdate_threadCert (hoA : ∀ j, j < 2 → argName j ≠ out) :
    ThreadCert (logicTau d 8 out) (([AL, AL] : Ctxt jasminDialect).length + 2)
      (logicS 8) out
      (straightOpsMem (([AL, AL] : Ctxt jasminDialect).length + 2) xorUpdate
        (([AL, AL] : Ctxt jasminDialect).length + 2))
      (([AL, AL] : Ctxt jasminDialect).length + 2)
      (accRegMN [AL, AL]) (loopBodyRetArrMN xorUpdate) := by
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [logicS], ?_⟩⟩
  · exact threadUses_args 1 2 4 (by omega)
  · exact threadArr_inv d 8 out 1 (by omega) hoA
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [logicS], ?_⟩⟩
  · exact threadUses_args 0 2 5 (by omega)
  · exact threadArr_inv d 8 out 0 (by omega) hoA
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [logicS], ?_⟩⟩
  · exact threadUses_regs 4 5 6 (by omega) (by omega)
  · exact threadArr_none d 8 out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [logicS], ?_⟩⟩
  · exact threadUses_reg 6 7 (by omega)
  · exact threadArr_none d 8 out
  refine ⟨?_, ?_, Or.inr ⟨rfl, rfl, rfl⟩⟩
  · exact threadUses_store 7 8 (by omega)
  · exact threadArr_acc d 8 out

/-- **The thread certificate of the `mpn_ior_n` chain.** The disjunction is
    synthesised from an exclusive-or and a conjunction, so its chain carries two
    slots more than the conjunction chain and stores at slot `10`. -/
theorem iorUpdate_threadCert (hoA : ∀ j, j < 2 → argName j ≠ out) :
    ThreadCert (logicTau d 10 out) (([AL, AL] : Ctxt jasminDialect).length + 2)
      (logicS 10) out
      (straightOpsMem (([AL, AL] : Ctxt jasminDialect).length + 2) iorUpdate
        (([AL, AL] : Ctxt jasminDialect).length + 2))
      (([AL, AL] : Ctxt jasminDialect).length + 2)
      (accRegMN [AL, AL]) (loopBodyRetArrMN iorUpdate) := by
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [logicS], ?_⟩⟩
  · exact threadUses_args 1 2 4 (by omega)
  · exact threadArr_inv d 10 out 1 (by omega) hoA
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [logicS], ?_⟩⟩
  · exact threadUses_args 0 2 5 (by omega)
  · exact threadArr_inv d 10 out 0 (by omega) hoA
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [logicS], ?_⟩⟩
  · exact threadUses_regs 4 5 6 (by omega) (by omega)
  · exact threadArr_none d 10 out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [logicS], ?_⟩⟩
  · exact threadUses_regs 4 5 7 (by omega) (by omega)
  · exact threadArr_none d 10 out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [logicS], ?_⟩⟩
  · exact threadUses_regs 6 7 8 (by omega) (by omega)
  · exact threadArr_none d 10 out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [logicS], ?_⟩⟩
  · exact threadUses_reg 8 9 (by omega)
  · exact threadArr_none d 10 out
  refine ⟨?_, ?_, Or.inr ⟨rfl, rfl, rfl⟩⟩
  · exact threadUses_store 9 10 (by omega)
  · exact threadArr_acc d 10 out

/-! ## 3. The canonicalised node computes the elementwise operation -/

/-- **The canonicalised `mpn_and_n` node computes the elementwise conjunction.**
    The canonicalised, aliased export loop node of the `mpn_and_n` kernel, run on
    the flag machine from program counter `0` with the seed agreement, readable
    invariant base registers and the trip count in `c`, halts with the array at
    `out` decoding to a value whose first `n` cells are the elementwise
    `List.zipWith` conjunction of the two source arrays. -/
theorem and_canon_machine_val (V : Ctxt.Valuation Gouter)
    (hn : (logicCount.lookup V).toNat ≤ NL)
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
    (hcnt : b0.reg.getW c 64
      = some (BitVec.ofNat 64 (logicCount.lookup V).toNat)) :
    ∃ (k : Nat) (t : LstateMF) (o : Fin NL → BitVec 64),
      lsemFuelMemF (singletonProgM fn
          (canonNodeRM (logicTau d 8 out) d out c andUpdate absent regs)) k
          { prog := { base := b0, lfn := fn }, zf := zf } = some t
        ∧ decodeArrM t.prog.base out 64 NL = some o
        ∧ cells o (logicCount.lookup V).toNat
            = List.zipWith (fun x y => x &&& y)
                (cells (apVar.lookup V) (logicCount.lookup V).toNat)
                (cells (bpVar.lookup V) (logicCount.lookup V).toNat) := by
  obtain ⟨k, t, hrun, hdec⟩ := canonNodeRM_faithful andUpdate andUpdate_arrMemN
    (logicTau_canonRen d 8 out hoR hoI hoC hoA) (andUpdate_threadCert d out hoA)
    absent regs hregs (Expr.lookupArgs logicInvs V) fn c hc b0 zf hpc
    (logicInit.lookup V) hseed hinv (logicCount.lookup V).toNat hm64 hcnt
  have heq : JLoopBodyN.denote ⟨(logicCount.lookup V).toNat, andUpdate⟩
        (Expr.lookupArgs logicInvs V) (logicInit.lookup V)
      = logicFold (fun x y => x &&& y) (apVar.lookup V) (bpVar.lookup V)
          (logicCount.lookup V).toNat (logicInit.lookup V) :=
    Option.some.inj ((logicRtProg_denote andSE andUpdate_eq V).symm.trans (andRtProg_fold V))
  refine ⟨k, t, _, hrun, hdec, ?_⟩
  rw [heq]
  exact andFold_cells (apVar.lookup V) (bpVar.lookup V) (logicInit.lookup V)
    (logicCount.lookup V).toNat hn

/-- **The canonicalised `mpn_xor_n` node computes the elementwise
    exclusive-or.** The exclusive-or analogue of `and_canon_machine_val`. -/
theorem xor_canon_machine_val (V : Ctxt.Valuation Gouter)
    (hn : (logicCount.lookup V).toNat ≤ NL)
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
    (hcnt : b0.reg.getW c 64
      = some (BitVec.ofNat 64 (logicCount.lookup V).toNat)) :
    ∃ (k : Nat) (t : LstateMF) (o : Fin NL → BitVec 64),
      lsemFuelMemF (singletonProgM fn
          (canonNodeRM (logicTau d 8 out) d out c xorUpdate absent regs)) k
          { prog := { base := b0, lfn := fn }, zf := zf } = some t
        ∧ decodeArrM t.prog.base out 64 NL = some o
        ∧ cells o (logicCount.lookup V).toNat
            = List.zipWith (fun x y => x ^^^ y)
                (cells (apVar.lookup V) (logicCount.lookup V).toNat)
                (cells (bpVar.lookup V) (logicCount.lookup V).toNat) := by
  obtain ⟨k, t, hrun, hdec⟩ := canonNodeRM_faithful xorUpdate xorUpdate_arrMemN
    (logicTau_canonRen d 8 out hoR hoI hoC hoA) (xorUpdate_threadCert d out hoA)
    absent regs hregs (Expr.lookupArgs logicInvs V) fn c hc b0 zf hpc
    (logicInit.lookup V) hseed hinv (logicCount.lookup V).toNat hm64 hcnt
  have heq : JLoopBodyN.denote ⟨(logicCount.lookup V).toNat, xorUpdate⟩
        (Expr.lookupArgs logicInvs V) (logicInit.lookup V)
      = logicFold (fun x y => x ^^^ y) (apVar.lookup V) (bpVar.lookup V)
          (logicCount.lookup V).toNat (logicInit.lookup V) :=
    Option.some.inj ((logicRtProg_denote xorSE xorUpdate_eq V).symm.trans (xorRtProg_fold V))
  refine ⟨k, t, _, hrun, hdec, ?_⟩
  rw [heq]
  exact xorFold_cells (apVar.lookup V) (bpVar.lookup V) (logicInit.lookup V)
    (logicCount.lookup V).toNat hn

/-- **The canonicalised `mpn_ior_n` node computes the elementwise
    disjunction.** The disjunction analogue of `and_canon_machine_val`, at the
    store slot `10` of the synthesised disjunction chain. -/
theorem ior_canon_machine_val (V : Ctxt.Valuation Gouter)
    (hn : (logicCount.lookup V).toNat ≤ NL)
    (hoR : ∀ k, out ≠ loopReg d k) (hoI : out ≠ loopIdx d) (hoC : out ≠ loopCtr d)
    (hoA : ∀ j, j < 2 → argName j ≠ out)
    (absent : Bool) (regs : List String)
    (hregs : ∀ r ∈ regs, ∃ j, j < ([AL, AL] : Ctxt jasminDialect).length ∧
      r = logicTau d 10 out (argName j))
    (fn c : String) (hc : c ≠ loopIdx d)
    (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0)
    (hseed : StoreAgreesM (([AL, AL] : Ctxt jasminDialect).length + 2)
      (([AL, AL] : Ctxt jasminDialect).length + 2)
      (pullM (logicTau d 10 out) (b0.setReg (loopIdx d) (0#64)))
      (tripValArrMN (Expr.lookupArgs logicInvs V) 0 (logicInit.lookup V)))
    (hinv : ∀ j, j < ([AL, AL] : Ctxt jasminDialect).length →
      (b0.reg.getW (logicTau d 10 out (argName j)) 64).isSome)
    (hm64 : (logicCount.lookup V).toNat < 2 ^ 64)
    (hcnt : b0.reg.getW c 64
      = some (BitVec.ofNat 64 (logicCount.lookup V).toNat)) :
    ∃ (k : Nat) (t : LstateMF) (o : Fin NL → BitVec 64),
      lsemFuelMemF (singletonProgM fn
          (canonNodeRM (logicTau d 10 out) d out c iorUpdate absent regs)) k
          { prog := { base := b0, lfn := fn }, zf := zf } = some t
        ∧ decodeArrM t.prog.base out 64 NL = some o
        ∧ cells o (logicCount.lookup V).toNat
            = List.zipWith (fun x y => x ||| y)
                (cells (apVar.lookup V) (logicCount.lookup V).toNat)
                (cells (bpVar.lookup V) (logicCount.lookup V).toNat) := by
  obtain ⟨k, t, hrun, hdec⟩ := canonNodeRM_faithful iorUpdate iorUpdate_arrMemN
    (logicTau_canonRen d 10 out hoR hoI hoC hoA) (iorUpdate_threadCert d out hoA)
    absent regs hregs (Expr.lookupArgs logicInvs V) fn c hc b0 zf hpc
    (logicInit.lookup V) hseed hinv (logicCount.lookup V).toNat hm64 hcnt
  have heq : JLoopBodyN.denote ⟨(logicCount.lookup V).toNat, iorUpdate⟩
        (Expr.lookupArgs logicInvs V) (logicInit.lookup V)
      = logicFold (fun x y => x ||| y) (apVar.lookup V) (bpVar.lookup V)
          (logicCount.lookup V).toNat (logicInit.lookup V) :=
    Option.some.inj ((logicRtProg_denote iorSE iorUpdate_eq V).symm.trans (iorRtProg_fold V))
  refine ⟨k, t, _, hrun, hdec, ?_⟩
  rw [heq]
  exact iorFold_cells (apVar.lookup V) (bpVar.lookup V) (logicInit.lookup V)
    (logicCount.lookup V).toNat hn

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanonLogic
