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
* **§4** `logicSigma`, `logicSigma_loopRen`, `logicSigma_comp_canonRen`: the
  exporter's loop renaming and its composition with a canonicalisation renaming.

The renamings and certificates of §1 are parametric in the loop depth, the store
slot and the output register, so they carry over to any chain of the same
argument layout whatever its limb count and slot names;
`JasminLsemExportCanonLogicShipped` instantiates them at the shipped
`mpn_and_n_loop_owned` body.
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
    export node at loop depth `d` with output register `out`, store slot `sl` and
    invariant base registers `i0`, `i1`: the accumulator argument and the store
    slot go to `out`, the index argument to the loop index, the two invariant
    arguments to `i0` and `i1`, every other chain register to its body temporary,
    every other name to itself. -/
noncomputable def logicTauG (d sl : Nat) (out i0 i1 : String) (r : String) : String :=
  if r = argName 3 then out
  else if r = argName 2 then loopIdx d
  else if r = argName 1 then i1
  else if r = argName 0 then i0
  else if r = regName sl then out
  else if h : ∃ k, r = regName k then loopReg d h.choose
  else r

variable (d sl : Nat) (out i0 i1 : String)

theorem logicTauG_argName3 : logicTauG d sl out i0 i1 (argName 3) = out := by
  simp [logicTauG]

theorem logicTauG_argName2 : logicTauG d sl out i0 i1 (argName 2) = loopIdx d := by
  simp [logicTauG, JasminLsemSimulation.argName_ne (show (2 : Nat) ≠ 3 by decide)]

theorem logicTauG_argName1 : logicTauG d sl out i0 i1 (argName 1) = i1 := by
  simp [logicTauG, JasminLsemSimulation.argName_ne (show (1 : Nat) ≠ 3 by decide),
    JasminLsemSimulation.argName_ne (show (1 : Nat) ≠ 2 by decide)]

theorem logicTauG_argName0 : logicTauG d sl out i0 i1 (argName 0) = i0 := by
  simp [logicTauG, JasminLsemSimulation.argName_ne (show (0 : Nat) ≠ 3 by decide),
    JasminLsemSimulation.argName_ne (show (0 : Nat) ≠ 2 by decide),
    JasminLsemSimulation.argName_ne (show (0 : Nat) ≠ 1 by decide)]

theorem logicTauG_regName_store : logicTauG d sl out i0 i1 (regName sl) = out := by
  simp [logicTauG, JasminLsemSimulation.regName_ne_argName]

theorem logicTauG_regName {k : Nat} (hk : k ≠ sl) :
    logicTauG d sl out i0 i1 (regName k) = loopReg d k := by
  have h7 : regName k ≠ regName sl := fun h => hk (JasminLsemSimulation.regName_injective h)
  have hex : ∃ k', regName k = regName k' := ⟨k, rfl⟩
  rw [logicTauG, if_neg (JasminLsemSimulation.regName_ne_argName k 3),
    if_neg (JasminLsemSimulation.regName_ne_argName k 2),
    if_neg (JasminLsemSimulation.regName_ne_argName k 1),
    if_neg (JasminLsemSimulation.regName_ne_argName k 0), if_neg h7, dif_pos hex,
    JasminLsemSimulation.regName_injective hex.choose_spec.symm]

theorem logicTauG_other {r : String} (h3' : r ≠ argName 3) (h2' : r ≠ argName 2)
    (h1' : r ≠ argName 1) (h0' : r ≠ argName 0) (h3 : ∀ k, r ≠ regName k) :
    logicTauG d sl out i0 i1 r = r := by
  rw [logicTauG, if_neg h3', if_neg h2', if_neg h1', if_neg h0', if_neg (h3 sl), dif_neg]
  rintro ⟨k, rfl⟩
  exact h3 k rfl

theorem logicTauG_loopCtr : logicTauG d sl out i0 i1 (loopCtr d) = loopCtr d :=
  logicTauG_other d sl out i0 i1 (loopCtr_ne_argName d 3) (loopCtr_ne_argName d 2)
    (loopCtr_ne_argName d 1) (loopCtr_ne_argName d 0) (loopCtr_ne_regName d)

theorem logicTauG_empty : logicTauG d sl out i0 i1 "" = "" :=
  logicTauG_other d sl out i0 i1
    (fun h => absurd h.symm (ne_empty_of_head? (head?_argName 3)))
    (fun h => absurd h.symm (ne_empty_of_head? (head?_argName 2)))
    (fun h => absurd h.symm (ne_empty_of_head? (head?_argName 1)))
    (fun h => absurd h.symm (ne_empty_of_head? (head?_argName 0)))
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

/-- **The logic family's renaming certificate.** A renaming `τ` satisfying the
    defining equations of the logic family's chain renaming — the empty name and
    the trip counter fixed, the store slot `sl` and the accumulator argument sent
    to `out`, the index argument to the loop index, the two invariant arguments
    to `i0` and `i1`, every other chain register to its body temporary — is a
    `CanonRen` at loop depth `d`, two invariants and the store-slot set
    `logicS sl`, whenever `out`, `i0` and `i1` are pairwise distinct and distinct
    from the loop index, the trip counter and every body temporary. -/
theorem canonRen_of (τ : String → String)
    (hE : τ "" = "") (hS : τ (regName sl) = out)
    (hR : ∀ k, k ≠ sl → τ (regName k) = loopReg d k)
    (e3 : τ (argName 3) = out) (e2 : τ (argName 2) = loopIdx d)
    (e1 : τ (argName 1) = i1) (e0 : τ (argName 0) = i0)
    (ectr : τ (loopCtr d) = loopCtr d)
    (hoR : ∀ k, out ≠ loopReg d k) (hoI : out ≠ loopIdx d) (hoC : out ≠ loopCtr d)
    (h0R : ∀ k, i0 ≠ loopReg d k) (h1R : ∀ k, i1 ≠ loopReg d k)
    (h0o : i0 ≠ out) (h1o : i1 ≠ out)
    (h0I : i0 ≠ loopIdx d) (h1I : i1 ≠ loopIdx d)
    (h0C : i0 ≠ loopCtr d) (h1C : i1 ≠ loopCtr d) :
    CanonRen τ d 2 (logicS sl) out where
  fix := hE
  tmp := by
    intro k _ hSk
    exact hR k (fun h => hSk h)
  thr := by
    intro k _ hSk
    have hk : k = sl := hSk
    subst hk
    exact hS
  arg := by
    intro j k hj
    interval_cases j
    · rw [e0]; exact h0R k
    · rw [e1]; exact h1R k
    · rw [e2]; exact loopIdx_ne_loopReg d d k
    · rw [e3]; exact hoR k
  outL := hoR
  acc := e3
  idx := e2
  ctr := ectr
  argOut := by
    intro j hj
    interval_cases j
    · rw [e0]; exact h0o
    · rw [e1]; exact h1o
    · rw [e2]; exact fun h => hoI h.symm
  invIdx := by
    intro j hj
    interval_cases j
    · rw [e0]; exact h0I
    · rw [e1]; exact h1I
  invCtr := by
    intro j hj
    interval_cases j
    · rw [e0]; exact h0C
    · rw [e1]; exact h1C
  outIdx := hoI
  outCtr := hoC
  idxCtr := loopIdx_ne_loopCtr d
  ctrL := loopCtr_ne_loopReg d d

/-- `logicTauG d sl out i0 i1` is a `CanonRen` at loop depth `d`, two invariants
    and the store-slot set `logicS sl`. -/
theorem logicTauG_canonRen
    (hoR : ∀ k, out ≠ loopReg d k) (hoI : out ≠ loopIdx d) (hoC : out ≠ loopCtr d)
    (h0R : ∀ k, i0 ≠ loopReg d k) (h1R : ∀ k, i1 ≠ loopReg d k)
    (h0o : i0 ≠ out) (h1o : i1 ≠ out)
    (h0I : i0 ≠ loopIdx d) (h1I : i1 ≠ loopIdx d)
    (h0C : i0 ≠ loopCtr d) (h1C : i1 ≠ loopCtr d) :
    CanonRen (logicTauG d sl out i0 i1) d 2 (logicS sl) out :=
  canonRen_of d sl out i0 i1 _ (logicTauG_empty d sl out i0 i1)
    (logicTauG_regName_store d sl out i0 i1)
    (fun _ hk => logicTauG_regName d sl out i0 i1 hk)
    (logicTauG_argName3 d sl out i0 i1) (logicTauG_argName2 d sl out i0 i1)
    (logicTauG_argName1 d sl out i0 i1) (logicTauG_argName0 d sl out i0 i1)
    (logicTauG_loopCtr d sl out i0 i1)
    hoR hoI hoC h0R h1R h0o h1o h0I h1I h0C h1C

/-- The renaming `logicTauG` at the invariant base registers `argName 0` and
    `argName 1`. -/
noncomputable def logicTau (d sl : Nat) (out : String) (r : String) : String :=
  logicTauG d sl out (argName 0) (argName 1) r

theorem logicTau_argName3 : logicTau d sl out (argName 3) = out :=
  logicTauG_argName3 d sl out (argName 0) (argName 1)

theorem logicTau_argName2 : logicTau d sl out (argName 2) = loopIdx d :=
  logicTauG_argName2 d sl out (argName 0) (argName 1)

theorem logicTau_regName_store : logicTau d sl out (regName sl) = out :=
  logicTauG_regName_store d sl out (argName 0) (argName 1)

theorem logicTau_regName {k : Nat} (hk : k ≠ sl) :
    logicTau d sl out (regName k) = loopReg d k :=
  logicTauG_regName d sl out (argName 0) (argName 1) hk

/-- The argument names other than the accumulator and the index are fixed. -/
theorem logicTau_argName_lt {j : Nat} (hj : j < 2) :
    logicTau d sl out (argName j) = argName j := by
  interval_cases j
  · exact logicTauG_argName0 d sl out (argName 0) (argName 1)
  · exact logicTauG_argName1 d sl out (argName 0) (argName 1)

theorem logicTau_other {r : String} (h1 : r ≠ argName 3) (h2 : r ≠ argName 2)
    (h3 : ∀ k, r ≠ regName k) : logicTau d sl out r = r := by
  by_cases hr1 : r = argName 1
  · subst hr1; exact logicTauG_argName1 d sl out (argName 0) (argName 1)
  by_cases hr0 : r = argName 0
  · subst hr0; exact logicTauG_argName0 d sl out (argName 0) (argName 1)
  exact logicTauG_other d sl out (argName 0) (argName 1) h1 h2 hr1 hr0 h3

theorem logicTau_loopCtr : logicTau d sl out (loopCtr d) = loopCtr d :=
  logicTauG_loopCtr d sl out (argName 0) (argName 1)

theorem logicTau_empty : logicTau d sl out "" = "" :=
  logicTauG_empty d sl out (argName 0) (argName 1)

/-- `logicTau d sl out` satisfies `CanonRen` at loop depth `d`, two invariants
    and the store-slot set `logicS sl`, whenever `out` is distinct from the loop
    index, the trip counter, every body temporary and the two invariant argument
    registers. -/
theorem logicTau_canonRen
    (hoR : ∀ k, out ≠ loopReg d k) (hoI : out ≠ loopIdx d) (hoC : out ≠ loopCtr d)
    (hoA : ∀ j, j < 2 → argName j ≠ out) :
    CanonRen (logicTau d sl out) d 2 (logicS sl) out :=
  logicTauG_canonRen d sl out (argName 0) (argName 1) hoR hoI hoC
    (argName_ne_loopReg d 0) (argName_ne_loopReg d 1) (hoA 0 (by omega)) (hoA 1 (by omega))
    (fun h => loopIdx_ne_argName d 0 h.symm) (fun h => loopIdx_ne_argName d 1 h.symm)
    (fun h => loopCtr_ne_argName d 0 h.symm) (fun h => loopCtr_ne_argName d 1 h.symm)

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
theorem threadArr_inv (τ : String → String) (j : Nat) (hj : τ (argName j) ≠ out) :
    ∀ b, some (argName j) = some b → τ b = out → b = argName 3 := by
  intro b hb hbo
  cases hb
  exact absurd hbo hj

/-- An instruction that touches no array passes the array-use condition. -/
theorem threadArr_none (τ : String → String) :
    ∀ b, (none : Option String) = some b → τ b = out → b = argName 3 := by
  intro b hb
  simp at hb

/-- A store through the accumulator argument passes the array-use condition: that
    argument is the thread head. -/
theorem threadArr_acc (τ : String → String) :
    ∀ b, some (argName 3) = some b → τ b = out → b = argName 3 := by
  intro b hb _
  cases hb
  rfl

/-- **The thread certificate of the `mpn_and_n` chain.** The chain loads the two
    source limbs from the invariant arrays, combines them, and stores the result
    through the accumulator argument, so its only store result is its last slot
    and the accumulator thread head never moves before it. -/
theorem andUpdate_threadCertT (τ : String → String)
    (h0o : τ (argName 0) ≠ out) (h1o : τ (argName 1) ≠ out) :
    ThreadCert τ (([AL, AL] : Ctxt jasminDialect).length + 2)
      (logicS 8) out
      (straightOpsMem (([AL, AL] : Ctxt jasminDialect).length + 2) andUpdate
        (([AL, AL] : Ctxt jasminDialect).length + 2))
      (([AL, AL] : Ctxt jasminDialect).length + 2)
      (accRegMN [AL, AL]) (loopBodyRetArrMN andUpdate) := by
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [logicS], ?_⟩⟩
  · exact threadUses_args 1 2 4 (by omega)
  · exact threadArr_inv out τ 1 h1o
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [logicS], ?_⟩⟩
  · exact threadUses_args 0 2 5 (by omega)
  · exact threadArr_inv out τ 0 h0o
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [logicS], ?_⟩⟩
  · exact threadUses_regs 4 5 6 (by omega) (by omega)
  · exact threadArr_none out τ
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [logicS], ?_⟩⟩
  · exact threadUses_reg 6 7 (by omega)
  · exact threadArr_none out τ
  refine ⟨?_, ?_, Or.inr ⟨rfl, rfl, rfl⟩⟩
  · exact threadUses_store 7 8 (by omega)
  · exact threadArr_acc out τ

/-- The thread certificate of the `mpn_and_n` chain at the invariant base
    registers `argName 0` and `argName 1`. -/
theorem andUpdate_threadCert (hoA : ∀ j, j < 2 → argName j ≠ out) :
    ThreadCert (logicTau d 8 out) (([AL, AL] : Ctxt jasminDialect).length + 2)
      (logicS 8) out
      (straightOpsMem (([AL, AL] : Ctxt jasminDialect).length + 2) andUpdate
        (([AL, AL] : Ctxt jasminDialect).length + 2))
      (([AL, AL] : Ctxt jasminDialect).length + 2)
      (accRegMN [AL, AL]) (loopBodyRetArrMN andUpdate) :=
  andUpdate_threadCertT out _
    (by rw [logicTau_argName_lt d 8 out (by omega)]; exact hoA 0 (by omega))
    (by rw [logicTau_argName_lt d 8 out (by omega)]; exact hoA 1 (by omega))

/-- **The thread certificate of the `mpn_xor_n` chain.** The exclusive-or chain
    has the shape of the conjunction chain, the combining instruction aside. -/
theorem xorUpdate_threadCertT (τ : String → String)
    (h0o : τ (argName 0) ≠ out) (h1o : τ (argName 1) ≠ out) :
    ThreadCert τ (([AL, AL] : Ctxt jasminDialect).length + 2)
      (logicS 8) out
      (straightOpsMem (([AL, AL] : Ctxt jasminDialect).length + 2) xorUpdate
        (([AL, AL] : Ctxt jasminDialect).length + 2))
      (([AL, AL] : Ctxt jasminDialect).length + 2)
      (accRegMN [AL, AL]) (loopBodyRetArrMN xorUpdate) := by
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [logicS], ?_⟩⟩
  · exact threadUses_args 1 2 4 (by omega)
  · exact threadArr_inv out τ 1 h1o
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [logicS], ?_⟩⟩
  · exact threadUses_args 0 2 5 (by omega)
  · exact threadArr_inv out τ 0 h0o
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [logicS], ?_⟩⟩
  · exact threadUses_regs 4 5 6 (by omega) (by omega)
  · exact threadArr_none out τ
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [logicS], ?_⟩⟩
  · exact threadUses_reg 6 7 (by omega)
  · exact threadArr_none out τ
  refine ⟨?_, ?_, Or.inr ⟨rfl, rfl, rfl⟩⟩
  · exact threadUses_store 7 8 (by omega)
  · exact threadArr_acc out τ

/-- The thread certificate of the `mpn_xor_n` chain at the invariant base
    registers `argName 0` and `argName 1`. -/
theorem xorUpdate_threadCert (hoA : ∀ j, j < 2 → argName j ≠ out) :
    ThreadCert (logicTau d 8 out) (([AL, AL] : Ctxt jasminDialect).length + 2)
      (logicS 8) out
      (straightOpsMem (([AL, AL] : Ctxt jasminDialect).length + 2) xorUpdate
        (([AL, AL] : Ctxt jasminDialect).length + 2))
      (([AL, AL] : Ctxt jasminDialect).length + 2)
      (accRegMN [AL, AL]) (loopBodyRetArrMN xorUpdate) :=
  xorUpdate_threadCertT out _
    (by rw [logicTau_argName_lt d 8 out (by omega)]; exact hoA 0 (by omega))
    (by rw [logicTau_argName_lt d 8 out (by omega)]; exact hoA 1 (by omega))

/-- **The thread certificate of the `mpn_ior_n` chain.** The disjunction is
    synthesised from an exclusive-or and a conjunction, so its chain carries two
    slots more than the conjunction chain and stores at slot `10`. -/
theorem iorUpdate_threadCertT (τ : String → String)
    (h0o : τ (argName 0) ≠ out) (h1o : τ (argName 1) ≠ out) :
    ThreadCert τ (([AL, AL] : Ctxt jasminDialect).length + 2)
      (logicS 10) out
      (straightOpsMem (([AL, AL] : Ctxt jasminDialect).length + 2) iorUpdate
        (([AL, AL] : Ctxt jasminDialect).length + 2))
      (([AL, AL] : Ctxt jasminDialect).length + 2)
      (accRegMN [AL, AL]) (loopBodyRetArrMN iorUpdate) := by
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [logicS], ?_⟩⟩
  · exact threadUses_args 1 2 4 (by omega)
  · exact threadArr_inv out τ 1 h1o
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [logicS], ?_⟩⟩
  · exact threadUses_args 0 2 5 (by omega)
  · exact threadArr_inv out τ 0 h0o
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [logicS], ?_⟩⟩
  · exact threadUses_regs 4 5 6 (by omega) (by omega)
  · exact threadArr_none out τ
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [logicS], ?_⟩⟩
  · exact threadUses_regs 4 5 7 (by omega) (by omega)
  · exact threadArr_none out τ
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [logicS], ?_⟩⟩
  · exact threadUses_regs 6 7 8 (by omega) (by omega)
  · exact threadArr_none out τ
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [logicS], ?_⟩⟩
  · exact threadUses_reg 8 9 (by omega)
  · exact threadArr_none out τ
  refine ⟨?_, ?_, Or.inr ⟨rfl, rfl, rfl⟩⟩
  · exact threadUses_store 9 10 (by omega)
  · exact threadArr_acc out τ

/-- The thread certificate of the `mpn_ior_n` chain at the invariant base
    registers `argName 0` and `argName 1`. -/
theorem iorUpdate_threadCert (hoA : ∀ j, j < 2 → argName j ≠ out) :
    ThreadCert (logicTau d 10 out) (([AL, AL] : Ctxt jasminDialect).length + 2)
      (logicS 10) out
      (straightOpsMem (([AL, AL] : Ctxt jasminDialect).length + 2) iorUpdate
        (([AL, AL] : Ctxt jasminDialect).length + 2))
      (([AL, AL] : Ctxt jasminDialect).length + 2)
      (accRegMN [AL, AL]) (loopBodyRetArrMN iorUpdate) :=
  iorUpdate_threadCertT out _
    (by rw [logicTau_argName_lt d 10 out (by omega)]; exact hoA 0 (by omega))
    (by rw [logicTau_argName_lt d 10 out (by omega)]; exact hoA 1 (by omega))

/-! ## 3. The canonicalised node computes the elementwise operation -/

/-- **The canonicalised `mpn_and_n` node computes the elementwise conjunction.**
    The canonicalised, aliased export loop node of the `mpn_and_n` kernel at the
    renaming `logicTauG d 8 out i0 i1`, run on the flag machine from program
    counter `0` with the seed agreement, readable invariant base registers and
    the trip count in `c`, halts with the array at `out` decoding to a value
    whose first `n` cells are the elementwise `List.zipWith` conjunction of the
    two source arrays. -/
theorem and_canon_machine_valT (τ : String → String) (V : Ctxt.Valuation Gouter)
    (hn : (logicCount.lookup V).toNat ≤ NL)
    (hτ : CanonRen τ d 2 (logicS 8) out)
    (h0o : τ (argName 0) ≠ out) (h1o : τ (argName 1) ≠ out)
    (absent : Bool) (regs : List String)
    (hregs : ∀ r ∈ regs, ∃ j, j < ([AL, AL] : Ctxt jasminDialect).length ∧
      r = τ (argName j))
    (fn c : String) (hc : c ≠ loopIdx d)
    (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0)
    (hseed : StoreAgreesM (([AL, AL] : Ctxt jasminDialect).length + 2)
      (([AL, AL] : Ctxt jasminDialect).length + 2)
      (pullM τ (b0.setReg (loopIdx d) (0#64)))
      (tripValArrMN (Expr.lookupArgs logicInvs V) 0 (logicInit.lookup V)))
    (hinv : ∀ j, j < ([AL, AL] : Ctxt jasminDialect).length →
      (b0.reg.getW (τ (argName j)) 64).isSome)
    (hm64 : (logicCount.lookup V).toNat < 2 ^ 64)
    (hcnt : b0.reg.getW c 64
      = some (BitVec.ofNat 64 (logicCount.lookup V).toNat)) :
    ∃ (k : Nat) (t : LstateMF) (o : Fin NL → BitVec 64),
      lsemFuelMemF (singletonProgM fn
          (canonNodeRM τ d out c andUpdate absent regs)) k
          { prog := { base := b0, lfn := fn }, zf := zf } = some t
        ∧ decodeArrM t.prog.base out 64 NL = some o
        ∧ cells o (logicCount.lookup V).toNat
            = List.zipWith (fun x y => x &&& y)
                (cells (apVar.lookup V) (logicCount.lookup V).toNat)
                (cells (bpVar.lookup V) (logicCount.lookup V).toNat) := by
  obtain ⟨k, t, hrun, hdec⟩ := canonNodeRM_faithful andUpdate andUpdate_arrMemN
    hτ (andUpdate_threadCertT out τ h0o h1o)
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

/-- `and_canon_machine_valT` at the renaming `logicTau d 8 out`. -/
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
                (cells (bpVar.lookup V) (logicCount.lookup V).toNat) :=
  and_canon_machine_valT d out _ V hn (logicTau_canonRen d 8 out hoR hoI hoC hoA)
    (by rw [logicTau_argName_lt d 8 out (by omega)]; exact hoA 0 (by omega))
    (by rw [logicTau_argName_lt d 8 out (by omega)]; exact hoA 1 (by omega))
    absent regs hregs fn c hc b0 zf hpc hseed hinv hm64 hcnt

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

/-! ## 4. The exporter's node of the `mpn_and_n` kernel -/

/-- The loop renaming of the elementwise binary kernels at loop depth `d`: the
    accumulator argument to the output argument `argName 0`, the index argument
    to the loop index, the two invariant arguments to their base registers
    `argName 2` and `argName 1`, every chain register to the body temporary of
    the same slot, every other name to itself. -/
noncomputable def logicSigma (d : Nat) (r : String) : String :=
  if r = argName 3 then argName 0
  else if r = argName 2 then loopIdx d
  else if r = argName 1 then argName 1
  else if r = argName 0 then argName 2
  else if h : ∃ k, r = regName k then loopReg d h.choose
  else r

theorem logicSigma_argName3 : logicSigma d (argName 3) = argName 0 := by
  simp [logicSigma]

theorem logicSigma_argName2 : logicSigma d (argName 2) = loopIdx d := by
  simp [logicSigma, JasminLsemSimulation.argName_ne (show (2 : Nat) ≠ 3 by decide)]

theorem logicSigma_argName1 : logicSigma d (argName 1) = argName 1 := by
  simp [logicSigma, JasminLsemSimulation.argName_ne (show (1 : Nat) ≠ 3 by decide),
    JasminLsemSimulation.argName_ne (show (1 : Nat) ≠ 2 by decide)]

theorem logicSigma_argName0 : logicSigma d (argName 0) = argName 2 := by
  simp [logicSigma, JasminLsemSimulation.argName_ne (show (0 : Nat) ≠ 3 by decide),
    JasminLsemSimulation.argName_ne (show (0 : Nat) ≠ 2 by decide),
    JasminLsemSimulation.argName_ne (show (0 : Nat) ≠ 1 by decide)]

theorem logicSigma_regName (k : Nat) : logicSigma d (regName k) = loopReg d k := by
  have hex : ∃ k', regName k = regName k' := ⟨k, rfl⟩
  rw [logicSigma, if_neg (JasminLsemSimulation.regName_ne_argName k 3),
    if_neg (JasminLsemSimulation.regName_ne_argName k 2),
    if_neg (JasminLsemSimulation.regName_ne_argName k 1),
    if_neg (JasminLsemSimulation.regName_ne_argName k 0), dif_pos hex,
    JasminLsemSimulation.regName_injective hex.choose_spec.symm]

theorem logicSigma_other {r : String} (h3' : r ≠ argName 3) (h2' : r ≠ argName 2)
    (h1' : r ≠ argName 1) (h0' : r ≠ argName 0) (h3 : ∀ k, r ≠ regName k) :
    logicSigma d r = r := by
  rw [logicSigma, if_neg h3', if_neg h2', if_neg h1', if_neg h0', dif_neg]
  rintro ⟨k, rfl⟩
  exact h3 k rfl

theorem logicSigma_loopCtr : logicSigma d (loopCtr d) = loopCtr d :=
  logicSigma_other d (loopCtr_ne_argName d 3) (loopCtr_ne_argName d 2)
    (loopCtr_ne_argName d 1) (loopCtr_ne_argName d 0) (loopCtr_ne_regName d)

theorem logicSigma_empty : logicSigma d "" = "" :=
  logicSigma_other d
    (fun h => absurd h.symm (ne_empty_of_head? (head?_argName 3)))
    (fun h => absurd h.symm (ne_empty_of_head? (head?_argName 2)))
    (fun h => absurd h.symm (ne_empty_of_head? (head?_argName 1)))
    (fun h => absurd h.symm (ne_empty_of_head? (head?_argName 0)))
    (fun k h => absurd h.symm (ne_empty_of_head? (head?_regName k)))

/-- **The loop renaming of the exporter's node.** `logicSigma d` is a `LoopRen`
    at loop depth `d`, two invariants, accumulator register `argName 0` and
    invariant base registers `[argName 1, argName 2]` — the registers
    `resolveVar` gives the kernel's four-argument outer context. -/
theorem logicSigma_loopRen :
    LoopRen (logicSigma d) d 2 (argName 0) [argName 1, argName 2] where
  acc := logicSigma_argName3 d
  idx := logicSigma_argName2 d
  inv := by
    intro j hj
    interval_cases j
    · exact logicSigma_argName0 d
    · exact logicSigma_argName1 d
  reg := logicSigma_regName d
  len := rfl

/-- **The canonicalisation renaming composed with the loop renaming.** A
    renaming `ρ` that sends the store slot's body temporary `loopReg d 8` to the
    output argument and fixes every other name composes with `logicSigma d` to a
    `CanonRen` at loop depth `d`, two invariants, store-slot set `logicS 8` and
    output `argName 0`. -/
theorem logicSigma_comp_canonRen (ρ : String → String)
    (hρid : ∀ r, r ≠ loopReg d 8 → ρ r = r) (hρ8 : ρ (loopReg d 8) = argName 0) :
    CanonRen (ρ ∘ logicSigma d) d 2 (logicS 8) (argName 0) :=
  canonRen_of d 8 (argName 0) (argName 2) (argName 1) (ρ ∘ logicSigma d)
    (by
      show ρ (logicSigma d "") = ""
      rw [logicSigma_empty]
      exact hρid _ (fun h => absurd h.symm (ne_empty_of_head? (head?_loopReg d 8))))
    (by show ρ (logicSigma d (regName 8)) = _; rw [logicSigma_regName]; exact hρ8)
    (fun k hk => by
      show ρ (logicSigma d (regName k)) = _
      rw [logicSigma_regName]
      exact hρid _ (fun h => hk (loopReg_injective d h)))
    (by
      show ρ (logicSigma d (argName 3)) = _
      rw [logicSigma_argName3]; exact hρid _ (argName_ne_loopReg d 0 8))
    (by
      show ρ (logicSigma d (argName 2)) = _
      rw [logicSigma_argName2]; exact hρid _ (loopIdx_ne_loopReg d d 8))
    (by
      show ρ (logicSigma d (argName 1)) = _
      rw [logicSigma_argName1]; exact hρid _ (argName_ne_loopReg d 1 8))
    (by
      show ρ (logicSigma d (argName 0)) = _
      rw [logicSigma_argName0]; exact hρid _ (argName_ne_loopReg d 2 8))
    (by
      show ρ (logicSigma d (loopCtr d)) = _
      rw [logicSigma_loopCtr]; exact hρid _ (loopCtr_ne_loopReg d d 8))
    (argName_ne_loopReg d 0) (fun h => loopIdx_ne_argName d 0 h.symm)
    (fun h => loopCtr_ne_argName d 0 h.symm)
    (argName_ne_loopReg d 2) (argName_ne_loopReg d 1)
    (JasminLsemSimulation.argName_ne (show (2 : Nat) ≠ 0 by decide))
    (JasminLsemSimulation.argName_ne (show (1 : Nat) ≠ 0 by decide))
    (fun h => loopIdx_ne_argName d 2 h.symm) (fun h => loopIdx_ne_argName d 1 h.symm)
    (fun h => loopCtr_ne_argName d 2 h.symm) (fun h => loopCtr_ne_argName d 1 h.symm)

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanonLogic
