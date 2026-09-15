/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LowCTMirrorTranslate
public import CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeProgram
public import CatCrypt.Crypto.Jasmin.LowCTToJasminImplOk

/-!
# The `LowCT` lowering and its `psem.v` mirror image run to corresponding states

`LowCTToJasmin.toJasminCmd` lowers a `LowCT` program to a JasminAST command, which
has two semantics: the `RawCode` translation `JasminTranslate.translateCmd` over a
heap, and, through `InstrRTranslateExt.translateCmdExt`, the relational semantics
`Sem` of the `psem.v` mirror. This module relates the two on the image of the
lowering.

## The state relation

`MirrorHeapCorr sid s heap` relates a mirror state to a heap at scope `sid`: every
`u64` register `x` of the mirror holds the word at the location of the JasminAST
variable `x : u64`, and every byte array `x` of `n` bytes holds the array at the
location of `x : u8[n]`. `getW`/`setW` and `getA`/`setA` read and write those
locations.

## The paired correspondence

`CorresTrans aS opS gd prog env sid P c c' fa` states that the JasminAST command `c`,
translated with enough fuel, evaluates from every heap with `P` to the single outcome
`fa heap` (`TransDet`), and that its mirror image `c'` corresponds at `fa`
(`ComJasminBridgeProgram.CorresSem` over `MirrorHeapCorr sid`). The mirror operator
tables are parameters; the lemmas assume the semantics of the operators they use:
`OpWordOfInt` and `OpWordNeq` for the expression operators, and `AsmStore64`,
`AsmCmov` and `AsmClone` for the tower pseudo-operations, which `towerAsmSem` satisfies.

## Main results

- `corresTrans_scalarSet`, `corresTrans_ifNz`, `corresTrans_limbStore`,
  `corresTrans_select`, `corresTrans_cloneTower`, `corresTrans_call`,
  `corresTrans_callN`: one lemma per emitted instruction shape; `RLetU64Zero` is
  `corresTrans_scalarSet` at `0`.
- `corresTrans_nil`, `corresTrans_append`, `corresTrans_unrollForJ`: composition.
- `ccall_arrs_semIr`, `ccall_arrsN_semIr`: the mirror call rules for array parameters
  and one or several array results.
- `corresSem_whileNz`: the loop `while (e ≠ (64u)0) { body }` corresponds, over the
  mirror `Sem` alone, at the iterate of the body's heap function at a first-failing
  count; `toJasminCmd_whileNz_mirror_exec` runs the lowered loop's mirror image.
- `toJasminCmd_corresTrans`: every program of `MirrorSimFragment` lowers to a command
  with a mirror image related by `CorresTrans`, given a `CorresTrans` for each call.
- `toJasminCmd_mirror_exec`: the mirror image runs under the fuel-bounded executor
  `execCmd` to a state related to the heap the `RawCode` translation produces.
- `u64OpSem_wordOfInt`, `u64OpSem_neq`, `towerAsmSem_store64`, `towerAsmSem_cmov`,
  `corresTrans_call_copy`, `corresTrans_callN_swap`: the operator and call hypotheses
  hold for concrete operator tables, for a call to a function returning its argument,
  and for a call to a function returning its two arguments swapped.
- `letZeroSetProg_mirror_exec`, `whileClearProg_mirror_exec`,
  `cloneCallProg_mirror_exec`, `swapCallProg_mirror_exec`: worked witnesses, one
  program each, run through the mirror by the rules.

## Scope

`RWhileNz` lowers to a `Cwhile` that the `RawCode` translation maps to failure, so the
loop has a `CorresSem` rule but no `CorresTrans` and is outside `MirrorSimFragment`;
`toJasminCmd_whileNz_mirror_exec` composes it with a fragment body.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LowCTMirrorCorres

open CatCrypt.Crypto.Jasmin.CoqSemMirror
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeProgram
open CatCrypt.Core (Heap)

/-- The heap of the `RawCode` translation. -/
abbrev AHeap := CatCrypt.Core.Heap

/-- The scope identifiers of the `RawCode` translation. -/
abbrev AScopeId := CatCrypt.Crypto.Jasmin.ScopeId

variable {SyscallState Mem : Type} [MemModel Mem]

/-! ## §1. The state relation -/

/-- The mirror `u64` register named `x`. -/
def mWordVar (x : String) : Var := { vname := x, vtype := .aword .U64 }

/-- The mirror byte array named `x` of `n` bytes. -/
def mArrVar (x : String) (n : Nat) : Var := { vname := x, vtype := .aarr .U8 n }

/-- The heap location of the JasminAST variable `x : u64` in scope `sid`. -/
noncomputable def aWordLoc (sid : AScopeId) (x : String) : CatCrypt.Core.Location :=
  CatCrypt.Crypto.Jasmin.wordLoc sid { vname := x, vtype := .sword .U64 } .U64

/-- The heap location of the JasminAST variable `x : u8[n]` in scope `sid`. -/
noncomputable def aArrLoc (sid : AScopeId) (x : String) (n : Nat) : CatCrypt.Core.Location :=
  CatCrypt.Crypto.Jasmin.arrLoc sid { vname := x, vtype := .sarr n } n

/-- The mirror `u64` word value. -/
def vW (w : BitVec 64) : Value := .Vword .U64 w

/-- The mirror `n`-byte array value. -/
def vA (n : Nat) (a : CatCrypt.Crypto.Jasmin.JArray n) : Value := .Varr n a

/-- The `u64` word at `x` in scope `sid`. -/
noncomputable def getW (heap : AHeap) (sid : AScopeId) (x : String) : BitVec 64 :=
  heap.get (aWordLoc sid x)

/-- The heap with the `u64` word `w` at `x` in scope `sid`. -/
noncomputable def setW (heap : AHeap) (sid : AScopeId) (x : String) (w : BitVec 64) : AHeap :=
  heap.set (aWordLoc sid x) w

/-- The `n`-byte array at `x` in scope `sid`. -/
noncomputable def getA (heap : AHeap) (sid : AScopeId) (x : String) (n : Nat) :
    CatCrypt.Crypto.Jasmin.JArray n :=
  heap.get (aArrLoc sid x n)

/-- The heap with the `n`-byte array `a` at `x` in scope `sid`. -/
noncomputable def setA (heap : AHeap) (sid : AScopeId) (x : String) (n : Nat)
    (a : CatCrypt.Crypto.Jasmin.JArray n) : AHeap :=
  heap.set (aArrLoc sid x n) a

/-- The mirror state `s` holds, at every `u64` register and every byte array, the
    value the heap holds at the location of the same JasminAST variable in scope `sid`. -/
def MirrorHeapCorr (sid : AScopeId) (s : Estate SyscallState Mem) (heap : AHeap) : Prop :=
  (∀ x, (s.evm).get (mWordVar x) = vW (getW heap sid x)) ∧
  (∀ x n, (s.evm).get (mArrVar x n) = vA n (getA heap sid x n))

/-- Word locations with different names are distinct. -/
theorem aWordLoc_id_ne (sid : AScopeId) (x y : String) (h : x ≠ y) :
    (aWordLoc sid x).id ≠ (aWordLoc sid y).id := by
  simp only [aWordLoc, CatCrypt.Crypto.Jasmin.wordLoc, CatCrypt.Crypto.Jasmin.varLocId]
  intro he
  exact h (CatCrypt.Crypto.Jasmin.encodeVarName_injective (Nat.pair_eq_pair.mp he).2)

/-- Array locations with different names or sizes are distinct. -/
theorem aArrLoc_id_ne (sid : AScopeId) (x y : String) (n m : Nat) (h : ¬ (x = y ∧ n = m)) :
    (aArrLoc sid x n).id ≠ (aArrLoc sid y m).id := by
  simp only [aArrLoc, CatCrypt.Crypto.Jasmin.arrLoc, CatCrypt.Crypto.Jasmin.varLocId]
  intro he
  have h1 := Nat.pair_eq_pair.mp he
  have h2 := (Nat.pair_eq_pair.mp h1.1).2
  simp only [CatCrypt.Crypto.Jasmin.encodeSType] at h2
  exact h ⟨CatCrypt.Crypto.Jasmin.encodeVarName_injective h1.2, by omega⟩

/-- A word location and an array location are distinct. -/
theorem aWordLoc_id_ne_aArrLoc (sid : AScopeId) (x y : String) (n : Nat) :
    (aWordLoc sid x).id ≠ (aArrLoc sid y n).id := by
  simp only [aWordLoc, aArrLoc, CatCrypt.Crypto.Jasmin.wordLoc, CatCrypt.Crypto.Jasmin.arrLoc,
    CatCrypt.Crypto.Jasmin.varLocId]
  intro he
  have h2 := (Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp he).1).2
  simp only [CatCrypt.Crypto.Jasmin.encodeSType, CatCrypt.Crypto.Jasmin.WSize.bits] at h2
  omega

theorem getW_setW_same (heap : AHeap) (sid : AScopeId) (x : String) (w : BitVec 64) :
    getW (setW heap sid x w) sid x = w :=
  Heap.get_set_same heap (aWordLoc sid x) w

theorem getW_setW_other (heap : AHeap) (sid : AScopeId) (x y : String) (w : BitVec 64)
    (h : x ≠ y) : getW (setW heap sid x w) sid y = getW heap sid y :=
  Heap.get_set_other heap (aWordLoc sid x) (aWordLoc sid y) w (aWordLoc_id_ne sid x y h)

theorem getA_setW (heap : AHeap) (sid : AScopeId) (x y : String) (n : Nat) (w : BitVec 64) :
    getA (setW heap sid x w) sid y n = getA heap sid y n :=
  Heap.get_set_other heap (aWordLoc sid x) (aArrLoc sid y n) w (aWordLoc_id_ne_aArrLoc sid x y n)

theorem getA_setA_same (heap : AHeap) (sid : AScopeId) (x : String) (n : Nat)
    (a : CatCrypt.Crypto.Jasmin.JArray n) : getA (setA heap sid x n a) sid x n = a :=
  Heap.get_set_same heap (aArrLoc sid x n) a

theorem getA_setA_other (heap : AHeap) (sid : AScopeId) (x y : String) (n m : Nat)
    (a : CatCrypt.Crypto.Jasmin.JArray n) (h : ¬ (x = y ∧ n = m)) :
    getA (setA heap sid x n a) sid y m = getA heap sid y m :=
  Heap.get_set_other heap (aArrLoc sid x n) (aArrLoc sid y m) a (aArrLoc_id_ne sid x y n m h)

theorem getW_setA (heap : AHeap) (sid : AScopeId) (x y : String) (n : Nat)
    (a : CatCrypt.Crypto.Jasmin.JArray n) : getW (setA heap sid x n a) sid y = getW heap sid y :=
  Heap.get_set_other heap (aArrLoc sid x n) (aWordLoc sid y) a
    (Ne.symm (aWordLoc_id_ne_aArrLoc sid y x n))

omit [MemModel Mem] in
/-- A paired register write preserves `MirrorHeapCorr`. -/
theorem mirrorHeapCorr_setWord (sid : AScopeId) (s : Estate SyscallState Mem) (heap : AHeap)
    (x : String) (w : BitVec 64) (h : MirrorHeapCorr sid s heap) :
    MirrorHeapCorr sid (s.withVm ((s.evm).set (mWordVar x) (vW w))) (setW heap sid x w) := by
  refine ⟨fun y => ?_, fun y n => ?_⟩
  · by_cases hxy : y = x
    · subst hxy
      simp only [Estate.withVm, Vm.get, Vm.set, decide_true, if_true, getW_setW_same]
    · have hv : mWordVar y ≠ mWordVar x := fun he => hxy (by cases he; rfl)
      simp only [Estate.withVm, Vm.get, Vm.set, hv, decide_false,
        getW_setW_other heap sid x y w (Ne.symm hxy)]
      exact h.1 y
  · have hv : mArrVar y n ≠ mWordVar x := fun he => by cases he
    simp only [Estate.withVm, Vm.get, Vm.set, hv, decide_false, getA_setW]
    exact h.2 y n

omit [MemModel Mem] in
/-- A paired array write preserves `MirrorHeapCorr`. -/
theorem mirrorHeapCorr_setArr (sid : AScopeId) (s : Estate SyscallState Mem) (heap : AHeap)
    (x : String) (n : Nat) (a : CatCrypt.Crypto.Jasmin.JArray n) (h : MirrorHeapCorr sid s heap) :
    MirrorHeapCorr sid (s.withVm ((s.evm).set (mArrVar x n) (vA n a))) (setA heap sid x n a) := by
  refine ⟨fun y => ?_, fun y m => ?_⟩
  · have hv : mWordVar y ≠ mArrVar x n := fun he => by cases he
    simp only [Estate.withVm, Vm.get, Vm.set, hv, decide_false, getW_setA]
    exact h.1 y
  · by_cases hxy : y = x ∧ m = n
    · obtain ⟨rfl, rfl⟩ := hxy
      simp only [Estate.withVm, Vm.get, Vm.set, decide_true, if_true, getA_setA_same]
    · have hv : mArrVar y m ≠ mArrVar x n := fun he => hxy (by cases he; exact ⟨rfl, rfl⟩)
      simp only [Estate.withVm, Vm.get, Vm.set, hv, decide_false]
      rw [getA_setA_other heap sid x y n m a (fun ⟨h1, h2⟩ => hxy ⟨h1.symm, h2.symm⟩)]
      exact h.2 y m

/-! ## §2. The paired correspondence -/

open CatCrypt.Crypto.Jasmin (TransEnv translateCmd)

/-- `c`, translated to `RawCode` at scope `sid` with enough fuel, evaluates from every
    heap satisfying `P` to the single outcome `fa heap`. -/
def TransDet (env : TransEnv) (sid : AScopeId) (P : AHeap → Prop)
    (c : CatCrypt.Crypto.Jasmin.Cmd) (fa : AHeap → AHeap) : Prop :=
  ∃ N, ∀ fuel, N ≤ fuel → ∀ heap, P heap →
    (translateCmd env c sid fuel).code.eval heap = CatCrypt.Prob.SDistr.pure (⟨()⟩, fa heap)

/-- The JasminAST command `c` evaluates deterministically to `fa`, and the mirror command
    `c'` corresponds at `fa` over `MirrorHeapCorr sid`. -/
def CorresTrans (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)
    (env : TransEnv) (sid : AScopeId) (P : AHeap → Prop)
    (c : CatCrypt.Crypto.Jasmin.Cmd) (c' : Cmd) (fa : AHeap → AHeap) : Prop :=
  TransDet env sid P c fa ∧
    CorresSem (SyscallState := SyscallState) (Mem := Mem) aS opS gd prog (MirrorHeapCorr sid) P fa c'

/-- The mirror operator table converts an integer to a `u64` word by `BitVec.ofInt`. -/
def OpWordOfInt (opS : OpSem) : Prop :=
  ∀ z : Int, opS.sem_sop1 (.Oword_of_int .U64) (.Vint z) = .ok (vW (BitVec.ofInt 64 z))

/-- The mirror operator table compares two `u64` words for inequality. -/
def OpWordNeq (opS : OpSem) : Prop :=
  ∀ a b : BitVec 64, opS.sem_sop2 (.Oneq (.Op_w .U64)) (vW a) (vW b) = .ok (.Vbool (a != b))

/-- The empty command. -/
theorem corresTrans_nil (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)
    (env : TransEnv) (sid : AScopeId) :
    CorresTrans (SyscallState := SyscallState) (Mem := Mem) aS opS gd prog env sid (fun _ => True)
      [] [] id := by
  refine ⟨⟨1, fun fuel hf heap _ => ?_⟩, corresSem_nil _⟩
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
  simp only [translateCmd, CatCrypt.Deep.eval_ret, CatCrypt.Core.SPComp.pure_def]
  rfl

/-- Strengthening the precondition. -/
theorem corresTrans_weaken {aS : AsmSem} {opS : OpSem} {gd : GlobDecls} {prog : Prog}
    {env : TransEnv} {sid : AScopeId} {P P' : AHeap → Prop}
    {c : CatCrypt.Crypto.Jasmin.Cmd} {c' : Cmd} {fa : AHeap → AHeap}
    (h : CorresTrans (SyscallState := SyscallState) (Mem := Mem) aS opS gd prog env sid P c c' fa)
    (hP : ∀ a, P' a → P a) :
    CorresTrans (SyscallState := SyscallState) (Mem := Mem) aS opS gd prog env sid P' c c' fa := by
  obtain ⟨⟨N, hN⟩, hS⟩ := h
  exact ⟨⟨N, fun fuel hf heap hp => hN fuel hf heap (hP heap hp)⟩, corresSem_weaken _ hS hP⟩

/-- Sequencing: `c1 ++ c2` and `c1' ++ c2'` correspond at `ga ∘ fa` when `fa` preserves
    `P`. The second command runs in the scope of the first, since the translation keeps
    the scope (`translateCmd_newSid`). -/
theorem corresTrans_append {aS : AsmSem} {opS : OpSem} {gd : GlobDecls} {prog : Prog}
    {env : TransEnv} {sid : AScopeId} {P : AHeap → Prop}
    {c1 c2 : CatCrypt.Crypto.Jasmin.Cmd} {c1' c2' : Cmd} {fa ga : AHeap → AHeap}
    (h1 : CorresTrans (SyscallState := SyscallState) (Mem := Mem) aS opS gd prog env sid P c1 c1' fa)
    (h2 : CorresTrans (SyscallState := SyscallState) (Mem := Mem) aS opS gd prog env sid P c2 c2' ga)
    (hinv : ∀ a, P a → P (fa a)) :
    CorresTrans (SyscallState := SyscallState) (Mem := Mem) aS opS gd prog env sid P
      (c1 ++ c2) (c1' ++ c2') (fun a => ga (fa a)) := by
  obtain ⟨⟨N1, hN1⟩, hS1⟩ := h1
  obtain ⟨⟨N2, hN2⟩, hS2⟩ := h2
  refine ⟨⟨max N1 (N2 + c1.length), fun fuel hf heap hp => ?_⟩, corresSem_append _ hS1 hS2 hinv⟩
  rw [CatCrypt.Crypto.Jasmin.LowCT.translateCmd_append_eval,
    CatCrypt.Crypto.Jasmin.translateCmd_newSid, hN1 fuel (by omega) heap hp,
    CatCrypt.Prob.SDistr.pure_bind]
  exact hN2 (fuel - c1.length) (by omega) (fa heap) (hinv heap hp)

/-! ## §3. Scalar constants and branches -/

/-- **`RScalarSet`.** The constant assignment `x := (64u) v` sets the word at `x`. -/
theorem corresTrans_scalarSet (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)
    (env : TransEnv) (sid : AScopeId) (x : String) (v : Nat) (hop : OpWordOfInt opS) :
    CorresTrans (SyscallState := SyscallState) (Mem := Mem) aS opS gd prog env sid (fun _ => True)
      [.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
        .AT_none (.sword .U64) (.Papp1 (.Oword_of_int .U64) (.Pconst (v : Int)))]
      [.MkI () (.Cassgn (.Lvar { v_var := mWordVar x }) .AT_none (.aword .U64)
        (.Papp1 (.Oword_of_int .U64) (.Pconst (v : Int))))]
      (fun heap => setW heap sid x (BitVec.ofNat 64 v)) := by
  refine ⟨⟨2, fun fuel hf heap _ => ?_⟩, ?_⟩
  · obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by omega⟩
    exact CatCrypt.Crypto.Jasmin.LowCT.translateCmd_cassgn_u64_val_eval env sid x v n heap
  · refine corresSem_instr _ () ?_
    intro s heap hSR _
    have hrhs : semPexpr (Mem := Mem) true gd opS s
        (.Papp1 (.Oword_of_int .U64) (.Pconst (v : Int))) = .ok (.Vword .U64 (BitVec.ofNat 64 v)) := by
      show opS.sem_sop1 (.Oword_of_int .U64) (.Vint (v : Int)) = _
      rw [hop, BitVec.ofInt_natCast]
      rfl
    refine ⟨_, ?_, mirrorHeapCorr_setWord sid s heap x (BitVec.ofNat 64 v) hSR⟩
    apply CatCrypt.Crypto.SecureCompilation.VIR.ExecAdequacy.execInstrR_sound (n := 1)
    rw [CatCrypt.Crypto.SecureCompilation.VIR.OpSemCoverage.execInstrR_Cassgn_eq]
    exact CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeFull.mirror_aword_assign_post
      gd opS { v_var := mWordVar x } .U64 _ _ s rfl hrhs

/-- The mirror guard `e ≠ (64u)0` of the lowered branch and loop on the scalar `e`. -/
def mirrorNeqZero (e : String) : Pexpr :=
  .Papp2 (.Oneq (.Op_w .U64)) (.Pvar (mkLvar { v_var := mWordVar e }))
    (.Papp1 (.Oword_of_int .U64) (.Pconst 0))

/-- The guard evaluates to whether the word at `e` is nonzero. -/
theorem semPexpr_mirrorNeqZero (gd : GlobDecls) (opS : OpSem) {sid : AScopeId} (e : String)
    (hop1 : OpWordOfInt opS) (hop2 : OpWordNeq opS) (s : Estate SyscallState Mem) (heap : AHeap)
    (hSR : MirrorHeapCorr sid s heap) :
    semPexpr (Mem := Mem) true gd opS s (mirrorNeqZero e) = .ok (.Vbool (getW heap sid e != 0)) := by
  have hv := CatCrypt.Crypto.SecureCompilation.VIR.OperandReadCorr.semPexpr_pvar_vword
    gd opS s { v_var := mWordVar e } .U64 (getW heap sid e) (hSR.1 e)
  have h0 : semPexpr (Mem := Mem) true gd opS s (.Papp1 (.Oword_of_int .U64) (.Pconst 0))
      = .ok (vW 0) := hop1 0
  show (do
    let v1 ← semPexpr (Mem := Mem) true gd opS s (.Pvar (mkLvar { v_var := mWordVar e }))
    let v2 ← semPexpr (Mem := Mem) true gd opS s (.Papp1 (.Oword_of_int .U64) (.Pconst 0))
    opS.sem_sop2 (.Oneq (.Op_w .U64)) v1 v2) = _
  rw [hv, h0]
  exact hop2 _ _

/-- **`RIfNz`.** The branch on `e ≠ 0` runs the branch the word at `e` selects. -/
theorem corresTrans_ifNz {aS : AsmSem} {opS : OpSem} {gd : GlobDecls} {prog : Prog}
    {env : TransEnv} {sid : AScopeId} {P : AHeap → Prop} (e : String)
    {ct cf : CatCrypt.Crypto.Jasmin.Cmd} {ct' cf' : Cmd} {fat faf : AHeap → AHeap}
    (hop1 : OpWordOfInt opS) (hop2 : OpWordNeq opS)
    (ht : CorresTrans (SyscallState := SyscallState) (Mem := Mem) aS opS gd prog env sid P ct ct' fat)
    (hf : CorresTrans (SyscallState := SyscallState) (Mem := Mem) aS opS gd prog env sid P cf cf' faf) :
    CorresTrans (SyscallState := SyscallState) (Mem := Mem) aS opS gd prog env sid P
      [.Cif (.Papp2 (.Oneq .U64)
          (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 }, info := {} }, gs := false })
          (.Papp1 (.Oword_of_int .U64) (.Pconst 0))) ct cf]
      [.MkI () (.Cif (.Papp2 (.Oneq (.Op_w .U64)) (.Pvar (mkLvar { v_var := mWordVar e }))
          (.Papp1 (.Oword_of_int .U64) (.Pconst 0))) ct' cf')]
      (fun heap => if getW heap sid e != 0 then fat heap else faf heap) := by
  obtain ⟨⟨Nt, hNt⟩, hSt⟩ := ht
  obtain ⟨⟨Nf, hNf⟩, hSf⟩ := hf
  refine ⟨⟨max Nt Nf + 1, fun fuel hfuel heap hp => ?_⟩, ?_⟩
  · obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
    have hc : (CatCrypt.Crypto.Jasmin.translatePExpr sid
        (.Papp2 (.Oneq .U64)
          (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 }, info := {} }, gs := false })
          (.Papp1 (.Oword_of_int .U64) (.Pconst 0)))).eval heap
        = CatCrypt.Prob.SDistr.pure (⟨.sbool, getW heap sid e != 0⟩, heap) :=
      CatCrypt.Crypto.Jasmin.LowCT.cif_cond_eval sid e heap
    cases hb : (getW heap sid e != 0) with
    | true =>
      rw [hb] at hc
      rw [CatCrypt.Crypto.Jasmin.LowCT.translateCmd_cif_eval_true env sid _ ct cf n heap heap hc,
        hNt n (by omega) heap hp]
      beta_reduce
      rw [if_pos hb]
    | false =>
      rw [hb] at hc
      rw [CatCrypt.Crypto.Jasmin.LowCT.translateCmd_cif_eval_false env sid _ ct cf n heap heap hc,
        CatCrypt.Crypto.Jasmin.translateCmd_newSid, hNf n (by omega) heap hp]
      beta_reduce
      rw [if_neg (by rw [hb]; decide)]
  · refine corresSem_instr _ () ?_
    intro s heap hSR hp
    have hcond := semPexpr_mirrorNeqZero gd opS e hop1 hop2 s heap hSR
    cases hb : (getW heap sid e != 0) with
    | true =>
      rw [hb] at hcond
      obtain ⟨s', hs', hSR'⟩ := hSt s heap hSR hp
      refine ⟨s', .Eif_true _ _ _ _ _ hcond hs', ?_⟩
      beta_reduce
      rw [if_pos hb]
      exact hSR'
    | false =>
      rw [hb] at hcond
      obtain ⟨s', hs', hSR'⟩ := hSf s heap hSR hp
      refine ⟨s', .Eif_false _ _ _ _ _ hcond hs', ?_⟩
      beta_reduce
      rw [if_neg (by rw [hb]; decide)]
      exact hSR'

/-! ## §3b. The loop on a scalar -/

open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeProgram (iterFold)

/-- **`RWhileNz`, over the mirror `Sem`.** Let the body `body'` correspond at `fb` from
    heaps with `P` and a nonzero word at `e`, let `fb` preserve `P` there, and let
    `count heap` be an iteration count at which the word at `e` first vanishes. Then the
    loop `while (e ≠ (64u)0) { body' }` corresponds at `iterFold fb (count heap)`. The
    `RawCode` translation of `Cwhile` is failure, so the loop has no `TransDet` half. -/
theorem corresSem_whileNz {aS : AsmSem} {opS : OpSem} {gd : GlobDecls} {prog : Prog}
    {sid : AScopeId} (e : String) (hop1 : OpWordOfInt opS) (hop2 : OpWordNeq opS)
    {P : AHeap → Prop} {body' : Cmd} {fb : AHeap → AHeap} (count : AHeap → Nat)
    (hB : CorresSem (SyscallState := SyscallState) (Mem := Mem) aS opS gd prog (MirrorHeapCorr sid)
      (fun heap => P heap ∧ getW heap sid e ≠ 0) fb body')
    (hinv : ∀ heap, P heap → getW heap sid e ≠ 0 → P (fb heap))
    (hcount : ∀ heap, P heap → (∀ j < count heap, getW (iterFold fb j heap) sid e ≠ 0) ∧
        getW (iterFold fb (count heap) heap) sid e = 0) :
    CorresSem (SyscallState := SyscallState) (Mem := Mem) aS opS gd prog (MirrorHeapCorr sid) P
      (fun heap => iterFold fb (count heap) heap)
      [.MkI () (.Cwhile .NoAlign [] (mirrorNeqZero e) () body')] := by
  refine corresSem_instr _ () ?_
  refine corresSem_while aS opS gd prog (MirrorHeapCorr sid) P (fun heap => getW heap sid e != 0)
    fb count .NoAlign (mirrorNeqZero e) () body' ?_ ?_ ?_ ?_
  · intro s heap hSR hP
    exact semPexpr_mirrorNeqZero gd opS e hop1 hop2 s heap hSR
  · intro s heap hSR hP hne
    exact hB s heap hSR ⟨hP, bne_iff_ne.mp hne⟩
  · intro heap hP hne
    exact hinv heap hP (bne_iff_ne.mp hne)
  · intro heap hP
    obtain ⟨h1, h2⟩ := hcount heap hP
    exact ⟨fun j hj => bne_iff_ne.mpr (h1 j hj), by simp [h2]⟩

/-! ## §4. Tower pseudo-operations -/

open CatCrypt.Crypto.Jasmin (JArray intToWord)

/-- The asm table writes, for `STORE64`, the 64-bit word little-endian at byte offset
    `8 * i` of the array. -/
def AsmStore64 (aS : AsmSem) : Prop :=
  ∀ (n : Nat) (a : JArray n) (i v : Int),
    aS.sopn_sem (.Oasm "STORE64") [vA n a, .Vint i, .Vint v]
      = .ok [vA n (JArray.setWord a .U64 (i.toNat * 8) (intToWord .U64 v))]

/-- The asm table selects, for `CMOV`, the first array when the word is `0` and the
    second otherwise. -/
def AsmCmov (aS : AsmSem) : Prop :=
  ∀ (n : Nat) (s : BitVec 64) (a b : JArray n),
    aS.sopn_sem (.Oasm "CMOV") [vW s, vA n a, vA n b] = .ok [if s = 0 then vA n a else vA n b]

/-- The asm table returns, for `CLONE_TOWER`, the array itself. -/
def AsmClone (aS : AsmSem) : Prop :=
  ∀ (n : Nat) (a : JArray n), aS.sopn_sem (.Oasm "CLONE_TOWER") [vA n a] = .ok [vA n a]

/-- `base` extended by the three tower pseudo-operations, with the argument and result
    conventions of `JasminOps.execSopn`. -/
def towerAsmSem (base : AsmSem) : AsmSem where
  sopn_sem := fun o vs =>
    match o, vs with
    | .Oasm "STORE64", [.Varr n a, .Vint i, .Vint v] =>
        .ok [.Varr n (JArray.setWord a .U64 (i.toNat * 8) (intToWord .U64 v))]
    | .Oasm "CMOV", [.Vword .U64 s, .Varr n a, .Varr m b] =>
        .ok [if s = 0 then .Varr n a else .Varr m b]
    | .Oasm "CLONE_TOWER", [.Varr n a] => .ok [.Varr n a]
    | o, vs => base.sopn_sem o vs

theorem towerAsmSem_store64 (base : AsmSem) : AsmStore64 (towerAsmSem base) :=
  fun _ _ _ _ => rfl

theorem towerAsmSem_cmov (base : AsmSem) : AsmCmov (towerAsmSem base) :=
  fun _ _ _ _ => rfl

theorem towerAsmSem_clone (base : AsmSem) : AsmClone (towerAsmSem base) :=
  fun _ _ => rfl

/-- Reading a local array variable. -/
theorem semPexpr_pvar_arr (gd : GlobDecls) (opS : OpSem) (s : Estate SyscallState Mem)
    (x : VarI) (n : Nat) (a : JArray n) (h : (s.evm).get x.v_var = vA n a) :
    semPexpr (Mem := Mem) true gd opS s (.Pvar (mkLvar x)) = .ok (vA n a) := by
  show getGvar true gd s.evm (mkLvar x) = _
  unfold getGvar
  rw [show (mkLvar x).isLvar = true from rfl]
  simp only [if_true]
  show getVar true s.evm (mkLvar x).gv.v_var = _
  unfold getVar
  rw [show (mkLvar x).gv.v_var = x.v_var from rfl, h]
  rfl

/-- Writing an array of the declared size to an array variable. -/
theorem writeLval_lvar_arr (gd : GlobDecls) (opS : OpSem) (s : Estate SyscallState Mem)
    (x : String) (n : Nat) (a : JArray n) :
    writeLval (Mem := Mem) true gd opS (.Lvar { v_var := mArrVar x n }) (vA n a) s
      = .ok (s.withVm ((s.evm).set (mArrVar x n) (vA n a))) := by
  show writeVar (Mem := Mem) true { v_var := mArrVar x n } (vA n a) s = _
  unfold writeVar setVar
  simp only [mArrVar, vA, DB, Value.isDefined, truncatable, Value.typeOf,
    Bool.not_true, decide_true, Bool.true_and, Bool.true_or]
  rfl

/-- **`RLimbStore`.** `STORE64` writes the word `v` at byte offset `8 * idx` of `loc`. -/
theorem corresTrans_limbStore {aS : AsmSem} (opS : OpSem) (gd : GlobDecls) (prog : Prog)
    (env : TransEnv) (sid : AScopeId) (hasm : AsmStore64 aS)
    (loc : CatCrypt.Crypto.Jasmin.LowCT.Located) (idx : Nat) (v : BitVec 64) :
    CorresTrans (SyscallState := SyscallState) (Mem := Mem) aS opS gd prog env sid (fun _ => True)
      [.Copn [CatCrypt.Crypto.Jasmin.LowCT.locToLVal loc] .AT_none (.Oasm { name := "STORE64" })
        [CatCrypt.Crypto.Jasmin.LowCT.locToPExpr loc, .Pconst idx, .Pconst v.toNat]]
      [.MkI () (.Copn [.Lvar { v_var := mArrVar loc.locVar loc.locSrc.storageBytes }] .AT_none
        (.Oasm "STORE64")
        [.Pvar (mkLvar { v_var := mArrVar loc.locVar loc.locSrc.storageBytes }),
          .Pconst idx, .Pconst v.toNat])]
      (fun heap => setA heap sid loc.locVar loc.locSrc.storageBytes
        (JArray.setWord (getA heap sid loc.locVar loc.locSrc.storageBytes) .U64 (idx * 8) v)) := by
  refine ⟨⟨2, fun fuel hf heap _ => ?_⟩, ?_⟩
  · obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by omega⟩
    exact CatCrypt.Crypto.Jasmin.LowCT.translateCmd_store64_eval env loc idx v sid n heap
  · refine corresSem_instr _ () ?_
    intro s heap hSR _
    refine ⟨_, .Eopn _ _ _ _ _ _ ?_, mirrorHeapCorr_setArr sid s heap _ _ _ hSR⟩
    have hargs := semPexpr_pvar_arr gd opS s
      { v_var := mArrVar loc.locVar loc.locSrc.storageBytes } _ _
      (hSR.2 loc.locVar loc.locSrc.storageBytes)
    show (do
      let vs ← semPexprList (Mem := Mem) true gd opS s
        [.Pvar (mkLvar { v_var := mArrVar loc.locVar loc.locSrc.storageBytes }),
          .Pconst idx, .Pconst v.toNat]
      let rs ← aS.sopn_sem (.Oasm "STORE64") vs
      writeLvals (Mem := Mem) true gd opS s
        [.Lvar { v_var := mArrVar loc.locVar loc.locSrc.storageBytes }] rs) = _
    simp only [semPexprList, hargs]
    show (do
      let rs ← aS.sopn_sem (.Oasm "STORE64")
        [vA _ (getA heap sid loc.locVar loc.locSrc.storageBytes), .Vint idx, .Vint v.toNat]
      writeLvals (Mem := Mem) true gd opS s
        [.Lvar { v_var := mArrVar loc.locVar loc.locSrc.storageBytes }] rs) = _
    rw [hasm]
    show (do
      let s1 ← writeLval (Mem := Mem) true gd opS
        (.Lvar { v_var := mArrVar loc.locVar loc.locSrc.storageBytes }) _ s
      writeLvals (Mem := Mem) true gd opS s1 [] []) = _
    rw [writeLval_lvar_arr]
    simp only [Int.toNat_natCast, CatCrypt.Crypto.Jasmin.LowCT.intToWord_U64_toNat]
    rfl

/-- **`RCloneCall`, first instruction.** `CLONE_TOWER` copies the array of `oldVar` to
    `cloneVar`. -/
theorem corresTrans_cloneTower {aS : AsmSem} (opS : OpSem) (gd : GlobDecls) (prog : Prog)
    (env : TransEnv) (sid : AScopeId) (hasm : AsmClone aS)
    (cloneVar oldVar : String) (t : CatCrypt.Crypto.Jasmin.LowCT.TowerType) :
    CorresTrans (SyscallState := SyscallState) (Mem := Mem) aS opS gd prog env sid (fun _ => True)
      [.Copn [.Lvar { var := { vname := cloneVar, vtype := .sarr t.storageBytes },
                      info := { towerTag := t.byteSize } }] .AT_none
            (.Oasm { name := "CLONE_TOWER" })
            [CatCrypt.Crypto.Jasmin.LowCT.locToPExpr { locVar := oldVar, locSrc := t }]]
      [.MkI () (.Copn [.Lvar { v_var := mArrVar cloneVar t.storageBytes }] .AT_none
        (.Oasm "CLONE_TOWER") [.Pvar (mkLvar { v_var := mArrVar oldVar t.storageBytes })])]
      (fun heap => setA heap sid cloneVar t.storageBytes (getA heap sid oldVar t.storageBytes)) := by
  refine ⟨⟨2, fun fuel hf heap _ => ?_⟩, ?_⟩
  · obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by omega⟩
    exact CatCrypt.Crypto.Jasmin.LowCT.translateCmd_cloneTower_eval env cloneVar oldVar t sid n heap
  · refine corresSem_instr _ () ?_
    intro s heap hSR _
    refine ⟨_, .Eopn _ _ _ _ _ _ ?_, mirrorHeapCorr_setArr sid s heap _ _ _ hSR⟩
    have hargs := semPexpr_pvar_arr gd opS s { v_var := mArrVar oldVar t.storageBytes }
      _ _ (hSR.2 oldVar t.storageBytes)
    show (do
      let vs ← semPexprList (Mem := Mem) true gd opS s
        [.Pvar (mkLvar { v_var := mArrVar oldVar t.storageBytes })]
      let rs ← aS.sopn_sem (.Oasm "CLONE_TOWER") vs
      writeLvals (Mem := Mem) true gd opS s [.Lvar { v_var := mArrVar cloneVar t.storageBytes }] rs)
      = _
    simp only [semPexprList, hargs]
    show (do
      let rs ← aS.sopn_sem (.Oasm "CLONE_TOWER") [vA _ (getA heap sid oldVar t.storageBytes)]
      writeLvals (Mem := Mem) true gd opS s [.Lvar { v_var := mArrVar cloneVar t.storageBytes }] rs)
      = _
    rw [hasm]
    show (do
      let s1 ← writeLval (Mem := Mem) true gd opS
        (.Lvar { v_var := mArrVar cloneVar t.storageBytes }) _ s
      writeLvals (Mem := Mem) true gd opS s1 [] []) = _
    rw [writeLval_lvar_arr]
    rfl

/-- **`RSelect`.** `CMOV` writes to `dstVar` the array of `x0` when the word at `sel` is
    `0` and the array of `x1` otherwise. -/
theorem corresTrans_select {aS : AsmSem} (opS : OpSem) (gd : GlobDecls) (prog : Prog)
    (env : TransEnv) (sid : AScopeId) (hasm : AsmCmov aS)
    (sel dstVar x0 x1 : String) (t : CatCrypt.Crypto.Jasmin.LowCT.TowerType) :
    CorresTrans (SyscallState := SyscallState) (Mem := Mem) aS opS gd prog env sid (fun _ => True)
      [.Copn [CatCrypt.Crypto.Jasmin.LowCT.locToLVal { locVar := dstVar, locSrc := t }] .AT_none
          (.Oasm { name := "CMOV" })
          [.Pvar { gv := { var := { vname := sel, vtype := .sword .U64 }, info := {} }, gs := false },
            CatCrypt.Crypto.Jasmin.LowCT.locToPExpr { locVar := x0, locSrc := t },
            CatCrypt.Crypto.Jasmin.LowCT.locToPExpr { locVar := x1, locSrc := t }]]
      [.MkI () (.Copn [.Lvar { v_var := mArrVar dstVar t.storageBytes }] .AT_none (.Oasm "CMOV")
        [.Pvar (mkLvar { v_var := mWordVar sel }),
          .Pvar (mkLvar { v_var := mArrVar x0 t.storageBytes }),
          .Pvar (mkLvar { v_var := mArrVar x1 t.storageBytes })])]
      (fun heap => setA heap sid dstVar t.storageBytes
        (if getW heap sid sel = 0 then getA heap sid x0 t.storageBytes
          else getA heap sid x1 t.storageBytes)) := by
  refine ⟨⟨2, fun fuel hf heap _ => ?_⟩, ?_⟩
  · obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by omega⟩
    exact CatCrypt.Crypto.Jasmin.LowCT.translateCmd_cmov_eval env sel dstVar x0 x1 t sid n heap
      (getW heap sid sel) rfl
  · refine corresSem_instr _ () ?_
    intro s heap hSR _
    refine ⟨_, .Eopn _ _ _ _ _ _ ?_, mirrorHeapCorr_setArr sid s heap _ _ _ hSR⟩
    have hsel := CatCrypt.Crypto.SecureCompilation.VIR.OperandReadCorr.semPexpr_pvar_vword
      gd opS s { v_var := mWordVar sel } .U64 (getW heap sid sel) (hSR.1 sel)
    have h0 := semPexpr_pvar_arr gd opS s { v_var := mArrVar x0 t.storageBytes }
      _ _ (hSR.2 x0 t.storageBytes)
    have h1 := semPexpr_pvar_arr gd opS s { v_var := mArrVar x1 t.storageBytes }
      _ _ (hSR.2 x1 t.storageBytes)
    show (do
      let vs ← semPexprList (Mem := Mem) true gd opS s
        [.Pvar (mkLvar { v_var := mWordVar sel }),
          .Pvar (mkLvar { v_var := mArrVar x0 t.storageBytes }),
          .Pvar (mkLvar { v_var := mArrVar x1 t.storageBytes })]
      let rs ← aS.sopn_sem (.Oasm "CMOV") vs
      writeLvals (Mem := Mem) true gd opS s [.Lvar { v_var := mArrVar dstVar t.storageBytes }] rs)
      = _
    simp only [semPexprList, hsel, h0, h1]
    show (do
      let rs ← aS.sopn_sem (.Oasm "CMOV") [vW (getW heap sid sel),
        vA _ (getA heap sid x0 t.storageBytes), vA _ (getA heap sid x1 t.storageBytes)]
      writeLvals (Mem := Mem) true gd opS s [.Lvar { v_var := mArrVar dstVar t.storageBytes }] rs)
      = _
    rw [hasm]
    by_cases hs : getW heap sid sel = 0
    · rw [if_pos hs, if_pos hs]
      show (do
        let s1 ← writeLval (Mem := Mem) true gd opS
          (.Lvar { v_var := mArrVar dstVar t.storageBytes }) _ s
        writeLvals (Mem := Mem) true gd opS s1 [] []) = _
      rw [writeLval_lvar_arr]
      rfl
    · rw [if_neg hs, if_neg hs]
      show (do
        let s1 ← writeLval (Mem := Mem) true gd opS
          (.Lvar { v_var := mArrVar dstVar t.storageBytes }) _ s
        writeLvals (Mem := Mem) true gd opS s1 [] []) = _
      rw [writeLval_lvar_arr]
      rfl

/-! ## §5. Calls with array parameters and an array result -/

/-- An array argument, parameter or result: the variable and the `n`-byte array it holds. -/
structure ArrArg where
  src : VarI
  n : Nat
  a : JArray n

/-- The value of an array argument. -/
def ArrArg.value (p : ArrArg) : Value := vA p.n p.a

/-- The read of an array argument. -/
def ArrArg.expr (p : ArrArg) : Pexpr := .Pvar (mkLvar p.src)

/-- The declared type of an array argument. -/
def ArrArg.ty (p : ArrArg) : Atype := .aarr .U8 p.n

/-- The variable map with the array parameters `ps` bound, left to right. -/
def paramVmA (ps : List ArrArg) (vm : Vm) : Vm :=
  ps.foldl (fun vm p => vm.set p.src.v_var p.value) vm

/-- Truncating an array at its own size is the identity. -/
theorem truncateVal_arr_self (n : Nat) (a : JArray n) :
    truncateVal (.carr n) (vA n a) = .ok (vA n a) := by
  show (do let a' ← JArrayMirror.cast (n := n) n a; (.ok (.Varr n a') : JResult Value)) = _
  simp [JArrayMirror.cast]
  rfl

/-- Truncating array arguments at their declared types is the identity. -/
theorem truncate_arrs : ∀ ps : List ArrArg,
    JResult.mapM (fun p : Atype × Value => truncateVal (evalAtype p.fst) p.snd)
      ((ps.map ArrArg.ty).zip (ps.map ArrArg.value)) = .ok (ps.map ArrArg.value)
  | [] => rfl
  | p :: ps => by
    show (do
        let b ← truncateVal (.carr p.n) (vA p.n p.a)
        let bs ← JResult.mapM (fun p : Atype × Value => truncateVal (evalAtype p.fst) p.snd)
          ((ps.map ArrArg.ty).zip (ps.map ArrArg.value))
        (.ok (b :: bs) : JResult Values)) = _
    rw [truncateVal_arr_self, truncate_arrs ps]
    rfl

omit [MemModel Mem] in
/-- Binding array parameters of their declared types is `paramVmA`. -/
theorem writeVars_arrs : ∀ (ps : List ArrArg) (s : Estate SyscallState Mem),
    (∀ p ∈ ps, p.src.v_var.vtype = p.ty) →
    writeVars (Mem := Mem) true (ps.map ArrArg.src) (ps.map ArrArg.value) s
      = .ok (s.withVm (paramVmA ps s.evm))
  | [], s, _ => rfl
  | p :: ps, s, h => by
    show (do
        let s1 ← writeVar (Mem := Mem) true p.src (vA p.n p.a) s
        writeVars (Mem := Mem) true (ps.map ArrArg.src) (ps.map ArrArg.value) s1) = _
    have hw : writeVar (Mem := Mem) true p.src (vA p.n p.a) s
        = .ok (s.withVm ((s.evm).set p.src.v_var (vA p.n p.a))) := by
      unfold writeVar setVar
      rw [h p List.mem_cons_self]
      simp only [ArrArg.ty, vA, DB, Value.isDefined, truncatable, Value.typeOf,
        Bool.not_true, decide_true, Bool.true_and, Bool.true_or]
      rfl
    rw [hw]
    show writeVars (Mem := Mem) true (ps.map ArrArg.src) (ps.map ArrArg.value)
        (s.withVm ((s.evm).set p.src.v_var (vA p.n p.a))) = _
    rw [writeVars_arrs ps _ (fun q hq => h q (List.mem_cons_of_mem p hq))]
    rfl

/-- Reading result variables that hold arrays. -/
theorem getVarIs_arrs (vm : Vm) : ∀ rs : List ArrArg,
    (∀ r ∈ rs, vm.get r.src.v_var = r.value) →
    getVarIs true vm (rs.map ArrArg.src) = .ok (rs.map ArrArg.value)
  | [], _ => rfl
  | r :: rs, h => by
    show (do
        let b ← getVar true vm r.src.v_var
        let bs ← getVarIs true vm (rs.map ArrArg.src)
        (.ok (b :: bs) : JResult Values)) = _
    have hg : getVar true vm r.src.v_var = .ok r.value := by
      unfold getVar
      rw [h r List.mem_cons_self]
      rfl
    rw [hg, getVarIs_arrs vm rs (fun q hq => h q (List.mem_cons_of_mem r hq))]
    rfl

/-- The mirror evaluates array arguments to their values. -/
theorem semPexprs_arrArgs (gd : GlobDecls) (opS : OpSem) (s : Estate SyscallState Mem) :
    ∀ (args : List ArrArg), (∀ a ∈ args, (s.evm).get a.src.v_var = a.value) →
      semPexprs (Mem := Mem) true gd opS s (args.map ArrArg.expr) = .ok (args.map ArrArg.value)
  | [], _ => rfl
  | a :: rest, h => by
    have ha := semPexpr_pvar_arr gd opS s a.src a.n a.a (h a List.mem_cons_self)
    have hrest := semPexprs_arrArgs gd opS s rest (fun b hb => h b (List.mem_cons_of_mem a hb))
    show (do
        let v ← semPexpr (Mem := Mem) true gd opS s a.expr
        let vs ← semPexprList (Mem := Mem) true gd opS s (rest.map ArrArg.expr)
        .ok (v :: vs)) = _
    rw [show a.expr = .Pvar (mkLvar a.src) from rfl, ha]
    show (do
        let vs ← semPexprs (Mem := Mem) true gd opS s (rest.map ArrArg.expr)
        (.ok (a.value :: vs) : JResult Values)) = _
    rw [hrest]
    rfl

/-- **The call rule for array parameters and an array result.** Let `fn` be defined in
    `prog` by `f`, with array parameters `ps` receiving the caller's argument arrays and
    one `n`-byte array result `ret`. If the callee body, started at the parameter map
    with the caller's memory and syscall state, has a derivation to `s2` in which `ret`
    holds `r`, then the call writes `r` into the caller's array `dst` and resumes with
    the memory and syscall state of `s2`. -/
theorem ccall_arrs_semIr (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)
    (fn : FunName) (f : FunDef) (hf : getFunDef prog fn = some f)
    (args ps : List ArrArg) (ret : VarI) (dst : String) (n : Nat) (r : JArray n)
    (s s2 : Estate SyscallState Mem)
    (hargs : ∀ a ∈ args, (s.evm).get a.src.v_var = a.value)
    (hps : ps.map ArrArg.value = args.map ArrArg.value)
    (htyin : f.tyin = ps.map ArrArg.ty) (hparams : f.params = ps.map ArrArg.src)
    (hpty : ∀ p ∈ ps, p.src.v_var.vtype = p.ty)
    (hbody : Sem aS opS gd prog
        { escs := s.escs, emem := s.emem, evm := paramVmA ps Vm.init } f.body s2)
    (hret : (s2.evm).get ret.v_var = vA n r)
    (htyout : f.tyout = [.aarr .U8 n]) (hretv : f.rets = [ret]) :
    SemIr aS opS gd prog s (.Ccall [.Lvar { v_var := mArrVar dst n }] fn (args.map ArrArg.expr))
      { escs := s2.escs, emem := s2.emem, evm := (s.evm).set (mArrVar dst n) (vA n r) } := by
  refine .Ecall s _ _ fn _ s2.escs s2.emem (args.map ArrArg.value) [vA n r]
    (semPexprs_arrArgs gd opS s args hargs) ?_ ?_
  · refine .EcallRun s.escs s.emem fn f (ps.map ArrArg.value) (args.map ArrArg.value)
      _ _ s2 [vA n r] [vA n r] hf ?_ rfl ?_ hbody ?_ ?_
    · rw [htyin, ← hps]; exact truncate_arrs ps
    · rw [hparams]; exact writeVars_arrs ps _ hpty
    · rw [hretv]; exact getVarIs_arrs _ [⟨ret, n, r⟩] (fun q hq => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
        subst hq; exact hret)
    · rw [htyout]; exact truncate_arrs [⟨ret, n, r⟩]
  · show (do
      let s1 ← writeLval (Mem := Mem) true gd opS (.Lvar { v_var := mArrVar dst n }) (vA n r)
        { s with emem := s2.emem, escs := s2.escs }
      writeLvals (Mem := Mem) true gd opS s1 [] []) = _
    rw [writeLval_lvar_arr]
    rfl

open CatCrypt.Crypto.Jasmin (TypedValue)
open CatCrypt.Crypto.Jasmin.LowCT

/-- The argument values a call to `args` reads at scope `sid`. -/
noncomputable def callArgVals (sid : AScopeId) (args : List Located) (heap : AHeap) :
    List TypedValue :=
  args.map (fun a => ⟨.sarr a.locSrc.storageBytes, getA heap sid a.locVar a.locSrc.storageBytes⟩)

/-- The caller-side array arguments of a call to `args`. -/
noncomputable def callArgArrs (sid : AScopeId) (args : List Located) (heap : AHeap) :
    List ArrArg :=
  args.map (fun a => ⟨{ v_var := mArrVar a.locVar a.locSrc.storageBytes },
    a.locSrc.storageBytes, getA heap sid a.locVar a.locSrc.storageBytes⟩)

/-- The callee parameters `pv` bound to the arrays of `args`. -/
noncomputable def calleeParamArrs (sid : AScopeId) (pv : List VarI) (args : List Located)
    (heap : AHeap) : List ArrArg :=
  (pv.zip args).map (fun pa => ⟨pa.1, pa.2.locSrc.storageBytes,
    getA heap sid pa.2.locVar pa.2.locSrc.storageBytes⟩)

/-- The callee parameters receive the caller's argument values, at the declared types,
    and are the variables `pv`. -/
theorem calleeParamArrs_props (sid : AScopeId) (heap : AHeap) :
    ∀ (pv : List VarI) (args : List Located), pv.length = args.length →
      (calleeParamArrs sid pv args heap).map ArrArg.value
          = (callArgArrs sid args heap).map ArrArg.value ∧
        (calleeParamArrs sid pv args heap).map ArrArg.ty
          = args.map (fun a => .aarr .U8 a.locSrc.storageBytes) ∧
        (calleeParamArrs sid pv args heap).map ArrArg.src = pv
  | [], [], _ => ⟨rfl, rfl, rfl⟩
  | p :: pv, a :: args, h => by
    obtain ⟨h1, h2, h3⟩ := calleeParamArrs_props sid heap pv args (by simpa using h)
    simp only [calleeParamArrs, callArgArrs, List.zip_cons_cons, List.map_cons] at h1 h2 h3 ⊢
    exact ⟨by rw [h1]; rfl, by rw [h2]; rfl, by rw [h3]⟩
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- The mirror image of the lowered call `RCall f dest args`. -/
def mirrorCallCmd (f : String) (dest : Located) (args : List Located) : Cmd :=
  [.MkI () (.Ccall [.Lvar { v_var := mArrVar dest.locVar dest.locSrc.storageBytes }]
    { name := f }
    (args.map (fun a => .Pvar (mkLvar { v_var := mArrVar a.locVar a.locSrc.storageBytes }))))]

/-- **`RCall`.** In the environment `pureLeafEnv g` whose function `f` returns the array
    `h` of its argument values, the call writes that array to `dest`, when the mirror
    callee `fd` has array parameters `pv` and an array result `ret` holding the same array
    at the end of its body. -/
theorem corresTrans_call {aS : AsmSem} (opS : OpSem) (gd : GlobDecls) (prog : Prog)
    (sid : AScopeId) (g : String → Option (List TypedValue → List TypedValue))
    (f : String) (dest : Located) (args : List Located)
    (h : List TypedValue → JArray dest.locSrc.storageBytes)
    (hg : g f = some (fun vs => [⟨.sarr dest.locSrc.storageBytes, h vs⟩]))
    (fd : FunDef) (hfd : getFunDef prog { name := f } = some fd) (pv : List VarI) (ret : VarI)
    (hlen : pv.length = args.length)
    (htyin : fd.tyin = args.map (fun a => .aarr .U8 a.locSrc.storageBytes))
    (hparams : fd.params = pv)
    (hpty : ∀ pa ∈ pv.zip args, pa.1.v_var.vtype = .aarr .U8 pa.2.locSrc.storageBytes)
    (htyout : fd.tyout = [.aarr .U8 dest.locSrc.storageBytes]) (hretv : fd.rets = [ret])
    (hbody : ∀ (scs : SyscallState) (mem : Mem) (heap : AHeap), ∃ s2,
      Sem aS opS gd prog (Estate.mk scs mem (paramVmA (calleeParamArrs sid pv args heap) Vm.init))
        fd.body s2 ∧
      (s2.evm).get ret.v_var = vA _ (h (callArgVals sid args heap))) :
    CorresTrans (SyscallState := SyscallState) (Mem := Mem) aS opS gd prog (pureLeafEnv g) sid
      (fun _ => True) (toJasminCmd (.RCall f dest args)) (mirrorCallCmd f dest args)
      (fun heap => setA heap sid dest.locVar dest.locSrc.storageBytes
        (h (callArgVals sid args heap))) := by
  rw [toJasminCmd_RCall]
  unfold mirrorCallCmd
  refine ⟨⟨2, fun fuel hf heap _ => ?_⟩, ?_⟩
  · obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by omega⟩
    refine translateCmd_ccall_pureLeafEnv_eval g [locToLVal dest] f args sid n heap _
      (fun gf hgf => ?_) (fun hn => by rw [hg] at hn; cases hn)
    rw [hg] at hgf
    cases hgf
    exact translateWriteLVals_locToLVal_eval sid dest _ heap
  · refine corresSem_instr _ () ?_
    intro s heap hSR _
    obtain ⟨s2, hs2, hret⟩ := hbody s.escs s.emem heap
    have hexpr : args.map
        (fun a => Pexpr.Pvar (mkLvar { v_var := mArrVar a.locVar a.locSrc.storageBytes }))
        = (callArgArrs sid args heap).map ArrArg.expr := by
      simp [callArgArrs, ArrArg.expr]
    rw [hexpr]
    refine ⟨_, ccall_arrs_semIr aS opS gd prog { name := f } fd hfd (callArgArrs sid args heap)
      (calleeParamArrs sid pv args heap) ret dest.locVar _ _ s s2 ?_ ?_ ?_ ?_ ?_ hs2 hret htyout
      hretv, ?_⟩
    · intro a ha
      simp only [callArgArrs, List.mem_map] at ha
      obtain ⟨b, _, rfl⟩ := ha
      exact hSR.2 b.locVar b.locSrc.storageBytes
    · exact (calleeParamArrs_props sid heap pv args hlen).1
    · rw [htyin, (calleeParamArrs_props sid heap pv args hlen).2.1]
    · rw [hparams, (calleeParamArrs_props sid heap pv args hlen).2.2]
    · intro p hp
      simp only [calleeParamArrs, List.mem_map] at hp
      obtain ⟨pa, hpa, rfl⟩ := hp
      exact hpty pa hpa
    · have hc := mirrorHeapCorr_setArr sid s heap dest.locVar dest.locSrc.storageBytes
        (h (callArgVals sid args heap)) hSR
      exact ⟨hc.1, hc.2⟩

/-! ## §5b. Calls with several array results -/

open CatCrypt.Crypto.Jasmin (translateWriteLVals translateWriteLVal writeVar_sarr_eq)

/-- Writing arrays of their declared sizes to array variables, in order, is `paramVmA`. -/
theorem writeLvals_arrs (gd : GlobDecls) (opS : OpSem) :
    ∀ (outs : List ArrArg) (s : Estate SyscallState Mem),
      (∀ o ∈ outs, o.src.v_var.vtype = o.ty) →
      writeLvals (Mem := Mem) true gd opS s (outs.map (fun o : ArrArg => Lval.Lvar o.src)) (outs.map ArrArg.value)
        = .ok (s.withVm (paramVmA outs s.evm))
  | [], _, _ => rfl
  | o :: outs, s, h => by
    show (do
        let s1 ← writeLval (Mem := Mem) true gd opS (.Lvar o.src) (vA o.n o.a) s
        writeLvals (Mem := Mem) true gd opS s1 (outs.map (fun o : ArrArg => Lval.Lvar o.src))
          (outs.map ArrArg.value)) = _
    have hw : writeLval (Mem := Mem) true gd opS (.Lvar o.src) (vA o.n o.a) s
        = .ok (s.withVm ((s.evm).set o.src.v_var (vA o.n o.a))) := by
      show writeVar (Mem := Mem) true o.src (vA o.n o.a) s = _
      unfold writeVar setVar
      rw [h o List.mem_cons_self]
      simp only [ArrArg.ty, vA, DB, Value.isDefined, truncatable, Value.typeOf,
        Bool.not_true, decide_true, Bool.true_and, Bool.true_or]
      rfl
    rw [hw]
    show writeLvals (Mem := Mem) true gd opS (s.withVm ((s.evm).set o.src.v_var (vA o.n o.a)))
        (outs.map (fun o : ArrArg => Lval.Lvar o.src)) (outs.map ArrArg.value) = _
    rw [writeLvals_arrs gd opS outs _ (fun q hq => h q (List.mem_cons_of_mem o hq))]
    rfl

/-- **The call rule for array parameters and several array results.** Let `fn` be
    defined in `prog` by `f`, with array parameters `ps` receiving the caller's argument
    arrays and array results `rets`. If the callee body, started at the parameter map
    with the caller's memory and syscall state, has a derivation to `s2` in which every
    result variable holds its array, then the call writes the result arrays into the
    caller's array variables `outs`, in order, and resumes with the memory and syscall
    state of `s2`. -/
theorem ccall_arrsN_semIr (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)
    (fn : FunName) (f : FunDef) (hf : getFunDef prog fn = some f)
    (args ps rets outs : List ArrArg) (s s2 : Estate SyscallState Mem)
    (hargs : ∀ a ∈ args, (s.evm).get a.src.v_var = a.value)
    (hps : ps.map ArrArg.value = args.map ArrArg.value)
    (htyin : f.tyin = ps.map ArrArg.ty) (hparams : f.params = ps.map ArrArg.src)
    (hpty : ∀ p ∈ ps, p.src.v_var.vtype = p.ty)
    (hbody : Sem aS opS gd prog
        { escs := s.escs, emem := s.emem, evm := paramVmA ps Vm.init } f.body s2)
    (hrets : ∀ r ∈ rets, (s2.evm).get r.src.v_var = r.value)
    (htyout : f.tyout = rets.map ArrArg.ty) (hretv : f.rets = rets.map ArrArg.src)
    (houts : outs.map ArrArg.value = rets.map ArrArg.value)
    (hoty : ∀ o ∈ outs, o.src.v_var.vtype = o.ty) :
    SemIr aS opS gd prog s (.Ccall (outs.map (fun o : ArrArg => Lval.Lvar o.src)) fn (args.map ArrArg.expr))
      { escs := s2.escs, emem := s2.emem, evm := paramVmA outs s.evm } := by
  refine .Ecall s _ _ fn _ s2.escs s2.emem (args.map ArrArg.value) (outs.map ArrArg.value)
    (semPexprs_arrArgs gd opS s args hargs) ?_ ?_
  · rw [houts]
    refine .EcallRun s.escs s.emem fn f (ps.map ArrArg.value) (args.map ArrArg.value)
      _ _ s2 (rets.map ArrArg.value) (rets.map ArrArg.value) hf ?_ rfl ?_ hbody ?_ ?_
    · rw [htyin, ← hps]; exact truncate_arrs ps
    · rw [hparams]; exact writeVars_arrs ps _ hpty
    · rw [hretv]; exact getVarIs_arrs _ rets hrets
    · rw [htyout]; exact truncate_arrs rets
  · exact writeLvals_arrs gd opS outs _ hoty

/-- An output of a lowered call: the destination location and the array it receives. -/
structure CallOut where
  loc : Located
  a : JArray loc.locSrc.storageBytes

/-- The typed value of an output. -/
def CallOut.typed (o : CallOut) : TypedValue := ⟨.sarr o.loc.locSrc.storageBytes, o.a⟩

/-- The heap after writing the outputs `outs`, in order. -/
noncomputable def writeOuts (sid : AScopeId) (outs : List CallOut) (heap : AHeap) : AHeap :=
  outs.foldl (fun hp o => setA hp sid o.loc.locVar o.loc.locSrc.storageBytes o.a) heap

/-- Writing the outputs to their tower variables is `writeOuts`. -/
theorem translateWriteLVals_callOuts_eval (sid : AScopeId) :
    ∀ (outs : List CallOut) (heap : AHeap),
      (translateWriteLVals sid (outs.map (fun o => locToLVal o.loc)) (outs.map CallOut.typed)).eval
        heap = CatCrypt.Prob.SDistr.pure (⟨()⟩, writeOuts sid outs heap)
  | [], heap => by
    simp only [List.map_nil, translateWriteLVals, writeOuts, List.foldl_nil,
      CatCrypt.Deep.eval_ret, CatCrypt.Core.SPComp.pure_def]
  | o :: outs, heap => by
    simp only [List.map_cons, translateWriteLVals, translateWriteLVal, CallOut.typed, locToLVal,
      locToVar, towerToSType, writeVar_sarr_eq, CatCrypt.Deep.eval_bind,
      CatCrypt.Core.SPComp.bind_def]
    exact (eval_put_bind_heap heap _ _ _).trans (translateWriteLVals_callOuts_eval sid outs _)

/-- The caller-side array variables receiving the outputs `outs`. -/
def callOutArrs (outs : List CallOut) : List ArrArg :=
  outs.map (fun o => ⟨{ v_var := mArrVar o.loc.locVar o.loc.locSrc.storageBytes },
    o.loc.locSrc.storageBytes, o.a⟩)

/-- The callee result variables `rv` holding the outputs `outs`. -/
def calleeRetArrs (rv : List VarI) (outs : List CallOut) : List ArrArg :=
  (rv.zip outs).map (fun ro => ⟨ro.1, ro.2.loc.locSrc.storageBytes, ro.2.a⟩)

/-- The callee results hold the output values, at the output types, and are the
    variables `rv`. -/
theorem calleeRetArrs_props :
    ∀ (rv : List VarI) (outs : List CallOut), rv.length = outs.length →
      (calleeRetArrs rv outs).map ArrArg.value = (callOutArrs outs).map ArrArg.value ∧
        (calleeRetArrs rv outs).map ArrArg.ty
          = outs.map (fun o => .aarr .U8 o.loc.locSrc.storageBytes) ∧
        (calleeRetArrs rv outs).map ArrArg.src = rv
  | [], [], _ => ⟨rfl, rfl, rfl⟩
  | r :: rv, o :: outs, h => by
    obtain ⟨h1, h2, h3⟩ := calleeRetArrs_props rv outs (by simpa using h)
    simp only [calleeRetArrs, callOutArrs, List.zip_cons_cons, List.map_cons] at h1 h2 h3 ⊢
    exact ⟨by rw [h1]; rfl, by rw [h2]; rfl, by rw [h3]⟩
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

omit [MemModel Mem] in
/-- The paired output writes preserve `MirrorHeapCorr`. -/
theorem mirrorHeapCorr_writeOuts (sid : AScopeId) :
    ∀ (outs : List CallOut) (s : Estate SyscallState Mem) (heap : AHeap),
      MirrorHeapCorr sid s heap →
      MirrorHeapCorr sid (s.withVm (paramVmA (callOutArrs outs) s.evm)) (writeOuts sid outs heap)
  | [], _, _, h => h
  | o :: outs, s, heap, h =>
    mirrorHeapCorr_writeOuts sid outs _ _
      (mirrorHeapCorr_setArr sid s heap o.loc.locVar o.loc.locSrc.storageBytes o.a h)

/-- The mirror image of the lowered multi-output call `RCallN f dests args`. -/
def mirrorCallNCmd (f : String) (dests args : List Located) : Cmd :=
  [.MkI () (.Ccall (dests.map (fun d => .Lvar { v_var := mArrVar d.locVar d.locSrc.storageBytes }))
    { name := f }
    (args.map (fun a => .Pvar (mkLvar { v_var := mArrVar a.locVar a.locSrc.storageBytes }))))]

theorem mirrorCallCmd_eq (f : String) (dest : Located) (args : List Located) :
    mirrorCallCmd f dest args = mirrorCallNCmd f [dest] args := rfl

/-- **`RCallN`.** In the environment `pureLeafEnv g` whose function `f` returns the
    outputs `h vs` of its argument values, laid out on `dests`, the call writes each
    output to its destination in order, when the mirror callee `fd` has array parameters
    `pv` and array results `rv` holding the outputs at the end of its body. -/
theorem corresTrans_callN {aS : AsmSem} (opS : OpSem) (gd : GlobDecls) (prog : Prog)
    (sid : AScopeId) (g : String → Option (List TypedValue → List TypedValue))
    (f : String) (dests args : List Located)
    (h : List TypedValue → List CallOut)
    (hshape : ∀ vs, (h vs).map CallOut.loc = dests)
    (hg : g f = some (fun vs => (h vs).map CallOut.typed))
    (fd : FunDef) (hfd : getFunDef prog { name := f } = some fd) (pv rv : List VarI)
    (hlen : pv.length = args.length) (hrlen : rv.length = dests.length)
    (htyin : fd.tyin = args.map (fun a => .aarr .U8 a.locSrc.storageBytes))
    (hparams : fd.params = pv)
    (hpty : ∀ pa ∈ pv.zip args, pa.1.v_var.vtype = .aarr .U8 pa.2.locSrc.storageBytes)
    (htyout : fd.tyout = dests.map (fun d => .aarr .U8 d.locSrc.storageBytes))
    (hretv : fd.rets = rv)
    (hbody : ∀ (scs : SyscallState) (mem : Mem) (heap : AHeap), ∃ s2,
      Sem aS opS gd prog (Estate.mk scs mem (paramVmA (calleeParamArrs sid pv args heap) Vm.init))
        fd.body s2 ∧
      ∀ ro ∈ rv.zip (h (callArgVals sid args heap)), (s2.evm).get ro.1.v_var = vA _ ro.2.a) :
    CorresTrans (SyscallState := SyscallState) (Mem := Mem) aS opS gd prog (pureLeafEnv g) sid
      (fun _ => True) (toJasminCmd (.RCallN f dests args)) (mirrorCallNCmd f dests args)
      (fun heap => writeOuts sid (h (callArgVals sid args heap)) heap) := by
  rw [toJasminCmd_RCallN]
  unfold mirrorCallNCmd
  refine ⟨⟨2, fun fuel hf heap _ => ?_⟩, ?_⟩
  · obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by omega⟩
    refine translateCmd_ccall_pureLeafEnv_eval g (dests.map locToLVal) f args sid n heap _
      (fun gf hgf => ?_) (fun hn => by rw [hg] at hn; cases hn)
    rw [hg] at hgf
    cases hgf
    rw [← hshape (callArgVals sid args heap), List.map_map]
    exact translateWriteLVals_callOuts_eval sid (h (callArgVals sid args heap)) heap
  · refine corresSem_instr _ () ?_
    intro s heap hSR _
    obtain ⟨s2, hs2, hret⟩ := hbody s.escs s.emem heap
    have hexpr : args.map
        (fun a => Pexpr.Pvar (mkLvar { v_var := mArrVar a.locVar a.locSrc.storageBytes }))
        = (callArgArrs sid args heap).map ArrArg.expr := by
      simp [callArgArrs, ArrArg.expr]
    have hlv : dests.map (fun d => Lval.Lvar { v_var := mArrVar d.locVar d.locSrc.storageBytes })
        = (callOutArrs (h (callArgVals sid args heap))).map (fun o : ArrArg => Lval.Lvar o.src) := by
      rw [← hshape (callArgVals sid args heap)]
      simp [callOutArrs]
    have hrl : rv.length = (h (callArgVals sid args heap)).length := by
      rw [hrlen, ← hshape (callArgVals sid args heap), List.length_map]
    obtain ⟨hr1, hr2, hr3⟩ := calleeRetArrs_props rv (h (callArgVals sid args heap)) hrl
    rw [hexpr, hlv]
    refine ⟨_, ccall_arrsN_semIr aS opS gd prog { name := f } fd hfd (callArgArrs sid args heap)
      (calleeParamArrs sid pv args heap) (calleeRetArrs rv (h (callArgVals sid args heap)))
      (callOutArrs (h (callArgVals sid args heap))) s s2 ?_ ?_ ?_ ?_ ?_ hs2 ?_ ?_ ?_ hr1.symm ?_, ?_⟩
    · intro a ha
      simp only [callArgArrs, List.mem_map] at ha
      obtain ⟨b, _, rfl⟩ := ha
      exact hSR.2 b.locVar b.locSrc.storageBytes
    · exact (calleeParamArrs_props sid heap pv args hlen).1
    · rw [htyin, (calleeParamArrs_props sid heap pv args hlen).2.1]
    · rw [hparams, (calleeParamArrs_props sid heap pv args hlen).2.2]
    · intro p hp
      simp only [calleeParamArrs, List.mem_map] at hp
      obtain ⟨pa, hpa, rfl⟩ := hp
      exact hpty pa hpa
    · intro r hr
      simp only [calleeRetArrs, List.mem_map] at hr
      obtain ⟨ro, hro, rfl⟩ := hr
      exact hret ro hro
    · rw [htyout, hr2, ← hshape (callArgVals sid args heap), List.map_map]
      rfl
    · rw [hretv, hr3]
    · intro o ho
      simp only [callOutArrs, List.mem_map] at ho
      obtain ⟨p, _, rfl⟩ := ho
      rfl
    · have hc := mirrorHeapCorr_writeOuts sid (h (callArgVals sid args heap)) s heap hSR
      exact ⟨hc.1, hc.2⟩

/-! ## §6. Composition over a `LowCT` fragment -/

open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslate
open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateExt
open CatCrypt.Crypto.SecureCompilation.VIR.LowCTMirrorTranslate

/-- The `LowCT` programs covered by `toJasminCmd_corresTrans`: skips, assertions,
    sequences, blocks, function definitions, scalar zero bindings, scalar constants,
    branches on a scalar, counted loops, literal limb stores, selections between
    locations of one tower type, calls `RCall`/`RCallN` whose name, destinations and
    arguments satisfy `callOk`, and clone calls whose cloned location has the clone's
    tower type and whose inner call satisfies `callOk`. -/
def MirrorSimFragment (callOk : String → List Located → List Located → Prop) : LowCT → Prop
  | .RSkip | .RAssert _ | .RScalarSet _ _ | .RLimbStore _ _ _ => True
  | .RSeq c1 c2 | .RIfNz _ c1 c2 | .RFnDef _ _ _ c1 c2 =>
      MirrorSimFragment callOk c1 ∧ MirrorSimFragment callOk c2
  | .RBlock body | .RFor _ _ body | .RLetU64Zero _ body => MirrorSimFragment callOk body
  | .RSelect dst _ src0 src1 => src0.locSrc = dst.locSrc ∧ src1.locSrc = dst.locSrc
  | .RCall f dest args => callOk f [dest] args
  | .RCallN f dests args => callOk f dests args
  | .RCloneCall _ ct od f dest args => od.locSrc = ct ∧ callOk f [dest] args
  | _ => False

/-- The translation of a concatenation whose parts translate. -/
theorem translateCmdExt_append_some {a b : CatCrypt.Crypto.Jasmin.Cmd} {a' b' : Cmd}
    (ha : translateCmdExt a = some a') (hb : translateCmdExt b = some b') :
    translateCmdExt (a ++ b) = some (a' ++ b') := by
  rw [translateCmdExt_append, ha, hb]

/-- The reads of tower locations translate to local array reads. -/
theorem mapM_translatePExprExt_locToPExpr : ∀ l : List Located,
    (l.map locToPExpr).mapM translatePExprExt
      = some (l.map (fun a => Pexpr.Pvar (mkLvar { v_var := mArrVar a.locVar a.locSrc.storageBytes })))
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, List.mapM_cons, mapM_translatePExprExt_locToPExpr l]
    simp [locToPExpr, locToGVar, locToVar, towerToSType, translatePExprExt, translateGVarExt,
      translateVarIExt, translateVarExt, translateSTypeExt, mArrVar, mkLvar]

/-- The mirror image of the lowered call is `mirrorCallCmd`. -/
theorem translateCmdExt_call (f : String) (dest : Located) (args : List Located) :
    translateCmdExt (toJasminCmd (.RCall f dest args)) = some (mirrorCallCmd f dest args) := by
  rw [toJasminCmd_RCall]
  simp only [translateCmdExt, translateInstrRExt, mapM_translatePExprExt_locToPExpr]
  simp [translateLValExt, locToLVal, locToVar, towerToSType, translateVarIExt, translateVarExt,
    translateSTypeExt, mirrorCallCmd, mArrVar]

/-- The l-values of tower locations translate to local array variables. -/
theorem mapM_translateLValExt_locToLVal : ∀ l : List Located,
    (l.map locToLVal).mapM translateLValExt
      = some (l.map (fun d => Lval.Lvar { v_var := mArrVar d.locVar d.locSrc.storageBytes }))
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, List.mapM_cons, mapM_translateLValExt_locToLVal l]
    simp [locToLVal, locToVar, towerToSType, translateLValExt, translateVarIExt, translateVarExt,
      translateSTypeExt, mArrVar]

/-- The mirror image of the lowered multi-output call is `mirrorCallNCmd`. -/
theorem translateCmdExt_callN (f : String) (dests args : List Located) :
    translateCmdExt (toJasminCmd (.RCallN f dests args)) = some (mirrorCallNCmd f dests args) := by
  rw [toJasminCmd_RCallN]
  simp only [translateCmdExt, translateInstrRExt, mapM_translatePExprExt_locToPExpr,
    mapM_translateLValExt_locToLVal]
  rfl

/-- The mirror image of the `CLONE_TOWER` instruction of a clone call. -/
theorem translateCmdExt_cloneTower (cloneVar : String) (t : TowerType) (oldVar : String) :
    translateCmdExt
      [.Copn [.Lvar { var := { vname := cloneVar, vtype := .sarr t.storageBytes },
                      info := { towerTag := t.byteSize } }] .AT_none
            (.Oasm { name := "CLONE_TOWER" }) [locToPExpr { locVar := oldVar, locSrc := t }]]
      = some [.MkI () (.Copn [.Lvar { v_var := mArrVar cloneVar t.storageBytes }] .AT_none
          (.Oasm "CLONE_TOWER") [.Pvar (mkLvar { v_var := mArrVar oldVar t.storageBytes })])] := by
  simp [translateCmdExt, translateInstrRExt, translateLValExt, translateVarIExt, translateVarExt,
    translateSTypeExt, locToPExpr, locToGVar, locToVar, towerToSType, translatePExprExt,
    translateGVarExt, mArrVar, mkLvar, translateAssgnTag]

/-- The mirror image of the lowered loop `RWhileNz e body` is the loop on
    `mirrorNeqZero e` over the image of the body. -/
theorem translateCmdExt_whileNz (e : String) (body : LowCT) {b : Cmd}
    (hb : translateCmdExt (toJasminCmd body) = some b) :
    translateCmdExt (toJasminCmd (.RWhileNz e body))
      = some [.MkI () (.Cwhile .NoAlign [] (mirrorNeqZero e) () b)] := by
  rw [toJasminCmd_RWhileNz]
  simp [translateCmdExt, translateInstrRExt, hb, translatePExprExt, translateSOp2Ext,
    translateWSize, translateGVarExt, translateVarIExt, translateVarExt, translateSTypeExt,
    translateSType, translateSOp1, translatePExpr, mirrorNeqZero, mWordVar, mkLvar]

/-- **The unrolled counted loop.** `n` copies of the index write followed by the body
    correspond when the body does. -/
theorem corresTrans_unrollForJ {aS : AsmSem} {opS : OpSem} {gd : GlobDecls} {prog : Prog}
    {env : TransEnv} {sid : AScopeId} (hop : OpWordOfInt opS) (x : String)
    {bodyJ : CatCrypt.Crypto.Jasmin.Cmd} {body' : Cmd} {fb : AHeap → AHeap}
    (hb : translateCmdExt bodyJ = some body')
    (hB : CorresTrans (SyscallState := SyscallState) (Mem := Mem) aS opS gd prog env sid
      (fun _ => True) bodyJ body' fb) :
    ∀ n, ∃ c' fa, translateCmdExt (unrollForJ x bodyJ n) = some c' ∧
      CorresTrans (SyscallState := SyscallState) (Mem := Mem) aS opS gd prog env sid
        (fun _ => True) (unrollForJ x bodyJ n) c' fa
  | 0 => ⟨[], id, rfl, corresTrans_nil aS opS gd prog env sid⟩
  | n + 1 => by
    obtain ⟨c', fa, hc', hC⟩ := corresTrans_unrollForJ hop x hb hB n
    have hS := corresTrans_scalarSet (SyscallState := SyscallState) (Mem := Mem) aS opS gd prog
      env sid x n hop
    have hSB := corresTrans_append hS hB (fun _ _ => trivial)
    refine ⟨_, _, ?_, corresTrans_append hC hSB (fun _ _ => trivial)⟩
    simp only [unrollForJ]
    refine translateCmdExt_append_some hc' ?_
    exact translateCmdExt_append_some (a := [_]) (by
      simp [translateCmdExt, translateInstrRExt, translateLValExt, translateVarIExt,
        translateVarExt, translateSTypeExt, translateSType, translateWSize, translatePExprExt,
        translateSOp1, translatePExpr, mWordVar, translateAssgnTag]) hb

/-- **Composition.** Every program of `MirrorSimFragment callOk` lowers to a command with
    a mirror image, and the two correspond, given a correspondence for each call that
    `callOk` admits, stated on the multi-output form (`RCall f dest args` is
    `RCallN f [dest] args`). -/
theorem toJasminCmd_corresTrans {aS : AsmSem} {opS : OpSem} {gd : GlobDecls} {prog : Prog}
    (env : TransEnv) (sid : AScopeId) (hop1 : OpWordOfInt opS) (hop2 : OpWordNeq opS)
    (hstore : AsmStore64 aS) (hcmov : AsmCmov aS) (hclone : AsmClone aS)
    (callOk : String → List Located → List Located → Prop)
    (hcall : ∀ f dests args, callOk f dests args → ∃ fa,
      CorresTrans (SyscallState := SyscallState) (Mem := Mem) aS opS gd prog env sid
        (fun _ => True) (toJasminCmd (.RCallN f dests args)) (mirrorCallNCmd f dests args) fa) :
    ∀ c, MirrorSimFragment callOk c → ∃ c' fa, translateCmdExt (toJasminCmd c) = some c' ∧
      CorresTrans (SyscallState := SyscallState) (Mem := Mem) aS opS gd prog env sid
        (fun _ => True) (toJasminCmd c) c' fa := by
  intro c hc
  induction c with
  | RSkip => exact ⟨[], id, rfl, corresTrans_nil aS opS gd prog env sid⟩
  | RAssert _ => exact ⟨[], id, rfl, corresTrans_nil aS opS gd prog env sid⟩
  | RSeq c1 c2 ih1 ih2 =>
    obtain ⟨c1', fa, h1, H1⟩ := ih1 hc.1
    obtain ⟨c2', ga, h2, H2⟩ := ih2 hc.2
    exact ⟨_, _, translateCmdExt_append_some h1 h2, corresTrans_append H1 H2 (fun _ _ => trivial)⟩
  | RFnDef _ _ _ c1 c2 ih1 ih2 =>
    obtain ⟨c1', fa, h1, H1⟩ := ih1 hc.1
    obtain ⟨c2', ga, h2, H2⟩ := ih2 hc.2
    exact ⟨_, _, translateCmdExt_append_some h1 h2, corresTrans_append H1 H2 (fun _ _ => trivial)⟩
  | RBlock body ih => exact ih hc
  | RLetU64Zero x body ih =>
    obtain ⟨b', fb, hb, HB⟩ := ih hc
    have hS := corresTrans_scalarSet (SyscallState := SyscallState) (Mem := Mem) aS opS gd prog
      env sid x 0 hop1
    refine ⟨_, _, ?_, corresTrans_append hS HB (fun _ _ => trivial)⟩
    rw [toJasminCmd_RLetU64Zero, ← List.singleton_append]
    exact translateCmdExt_append_some (a := [_]) (by
      simp [translateCmdExt, translateInstrRExt, translateLValExt, translateVarIExt,
        translateVarExt, translateSTypeExt, translateSType, translateWSize, translatePExprExt,
        translateSOp1, translatePExpr, mWordVar, translateAssgnTag]) hb
  | RScalarSet x v =>
    refine ⟨_, _, ?_, corresTrans_scalarSet aS opS gd prog env sid x v hop1⟩
    simp [translateCmdExt, translateInstrRExt, translateLValExt, translateVarIExt,
      translateVarExt, translateSTypeExt, translateSType, translateWSize, translatePExprExt,
      translateSOp1, translatePExpr, mWordVar, translateAssgnTag]
  | RIfNz e ct cf ih1 ih2 =>
    obtain ⟨ct', fat, h1, H1⟩ := ih1 hc.1
    obtain ⟨cf', faf, h2, H2⟩ := ih2 hc.2
    refine ⟨_, _, ?_, corresTrans_ifNz e hop1 hop2 H1 H2⟩
    simp [translateCmdExt, translateInstrRExt, h1, h2, translatePExprExt, translateSOp2Ext,
      translateWSize, translateGVarExt, translateVarIExt, translateVarExt, translateSTypeExt,
      translateSType, translateSOp1, translatePExpr, mWordVar, mkLvar]
  | RFor x n body ih =>
    obtain ⟨b', fb, hb, HB⟩ := ih hc
    exact corresTrans_unrollForJ hop1 x hb HB n
  | RLimbStore loc idx v =>
    refine ⟨_, _, ?_, corresTrans_limbStore opS gd prog env sid hstore loc idx v⟩
    simp [translateCmdExt, translateInstrRExt, translateLValExt, locToLVal, locToPExpr,
      locToGVar, locToVar, towerToSType, translateVarIExt, translateVarExt, translateSTypeExt,
      translatePExprExt, translateGVarExt, translatePExpr, mArrVar, mkLvar, translateAssgnTag]
  | RSelect dst sel src0 src1 =>
    obtain ⟨h0, h1⟩ := hc
    obtain ⟨d, t⟩ := dst
    obtain ⟨x0, t0⟩ := src0
    obtain ⟨x1, t1⟩ := src1
    simp only at h0 h1
    subst h0 h1
    refine ⟨_, _, ?_, corresTrans_select opS gd prog env sid hcmov sel d x0 x1 _⟩
    simp [translateCmdExt, translateInstrRExt, translateLValExt, locToLVal, locToPExpr,
      locToGVar, locToVar, towerToSType, translateVarIExt, translateVarExt, translateSTypeExt,
      translatePExprExt, translateGVarExt, translateSType, translateWSize,
      mArrVar, mWordVar, mkLvar, translateAssgnTag]
  | RCall f dest args =>
    obtain ⟨fa, H⟩ := hcall f [dest] args hc
    exact ⟨_, fa, translateCmdExt_call f dest args, H⟩
  | RCallN f dests args =>
    obtain ⟨fa, H⟩ := hcall f dests args hc
    exact ⟨_, fa, translateCmdExt_callN f dests args, H⟩
  | RCloneCall cv ct od f dest args =>
    obtain ⟨hod, hok⟩ := hc
    obtain ⟨ov, ot⟩ := od
    simp only at hod
    subst hod
    obtain ⟨fa, H⟩ := hcall f [dest] args hok
    refine ⟨_, _, ?_, corresTrans_append
      (corresTrans_cloneTower opS gd prog env sid hclone cv ov ot) H (fun _ _ => trivial)⟩
    exact translateCmdExt_append_some (translateCmdExt_cloneTower cv ot ov)
      (translateCmdExt_callN f [dest] args)
  | _ => exact hc.elim

/-- **End to end.** For a program of the fragment, from a mirror state related to a heap,
    the `RawCode` translation evaluates at every fuel from some bound on to one heap, and
    the mirror image runs under the fuel-bounded executor `execCmd` to a state related to
    that heap. -/
theorem toJasminCmd_mirror_exec {aS : AsmSem} {opS : OpSem} {gd : GlobDecls} {prog : Prog}
    (env : TransEnv) (sid : AScopeId) (hop1 : OpWordOfInt opS) (hop2 : OpWordNeq opS)
    (hstore : AsmStore64 aS) (hcmov : AsmCmov aS) (hclone : AsmClone aS)
    (callOk : String → List Located → List Located → Prop)
    (hcall : ∀ f dests args, callOk f dests args → ∃ fa,
      CorresTrans (SyscallState := SyscallState) (Mem := Mem) aS opS gd prog env sid
        (fun _ => True) (toJasminCmd (.RCallN f dests args)) (mirrorCallNCmd f dests args) fa)
    (c : LowCT) (hc : MirrorSimFragment callOk c)
    (s : Estate SyscallState Mem) (heap : AHeap) (hSR : MirrorHeapCorr sid s heap) :
    ∃ c' heap', translateCmdExt (toJasminCmd c) = some c' ∧
      (∃ N, ∀ fuel, N ≤ fuel →
        (translateCmd env (toJasminCmd c) sid fuel).code.eval heap
          = CatCrypt.Prob.SDistr.pure (⟨()⟩, heap')) ∧
      ∃ s' fuel, execCmd aS opS gd fuel s c' prog = .ok s' ∧ MirrorHeapCorr sid s' heap' := by
  obtain ⟨c', fa, hc', ⟨N, hN⟩, hS⟩ :=
    toJasminCmd_corresTrans env sid hop1 hop2 hstore hcmov hclone callOk hcall c hc
  obtain ⟨s', fuel, hrun, hSR'⟩ := corresSem_exec _ hS s heap hSR trivial
  exact ⟨c', fa heap, hc', ⟨N, fun fuel' hf => hN fuel' hf heap trivial⟩, s', fuel, hrun, hSR'⟩

/-- **`RWhileNz` end to end.** For a loop whose body lowers to a command with mirror
    image `b'` corresponding at `fb`, and an iteration count `count` at which the word at
    `e` first vanishes along the iterates of `fb`, the lowered loop has the mirror image
    `while (e ≠ (64u)0) { b' }`, which runs under `execCmd` from every state related to a
    heap to a state related to `iterFold fb (count heap) heap`. -/
theorem toJasminCmd_whileNz_mirror_exec {aS : AsmSem} {opS : OpSem} {gd : GlobDecls}
    {prog : Prog} (env : TransEnv) (sid : AScopeId) (hop1 : OpWordOfInt opS)
    (hop2 : OpWordNeq opS) (e : String) (body : LowCT) {b' : Cmd} {fb : AHeap → AHeap}
    (hb : translateCmdExt (toJasminCmd body) = some b')
    (hB : CorresTrans (SyscallState := SyscallState) (Mem := Mem) aS opS gd prog env sid
      (fun _ => True) (toJasminCmd body) b' fb)
    (count : AHeap → Nat)
    (hcount : ∀ heap, (∀ j < count heap, getW (iterFold fb j heap) sid e ≠ 0) ∧
        getW (iterFold fb (count heap) heap) sid e = 0) :
    translateCmdExt (toJasminCmd (.RWhileNz e body))
        = some [.MkI () (.Cwhile .NoAlign [] (mirrorNeqZero e) () b')] ∧
      ∀ (s : Estate SyscallState Mem) (heap : AHeap), MirrorHeapCorr sid s heap →
        ∃ s' fuel, execCmd aS opS gd fuel s
            [.MkI () (.Cwhile .NoAlign [] (mirrorNeqZero e) () b')] prog = .ok s' ∧
          MirrorHeapCorr sid s' (iterFold fb (count heap) heap) := by
  refine ⟨translateCmdExt_whileNz e body hb, fun s heap hSR => ?_⟩
  have hW := corresSem_whileNz (aS := aS) (opS := opS) (gd := gd) (prog := prog)
    (sid := sid) e hop1 hop2 (P := fun _ => True) count
    (corresSem_weaken _ hB.2 (fun _ _ => trivial)) (fun _ _ _ => trivial)
    (fun heap _ => hcount heap)
  exact corresSem_exec _ hW s heap hSR trivial

/-! ## §7. Instances of the hypotheses -/

/-- `base` with the `u64` conversion `Oword_of_int U64` and the `u64` inequality
    `Oneq (Op_w U64)`. -/
def u64OpSem (base : OpSem) : OpSem where
  sem_sop1 := fun o v =>
    match o, v with
    | .Oword_of_int .U64, .Vint z => .ok (.Vword .U64 (BitVec.ofInt 64 z))
    | o, v => base.sem_sop1 o v
  sem_sop2 := fun o v1 v2 =>
    match o, v1, v2 with
    | .Oneq (.Op_w .U64), .Vword .U64 a, .Vword .U64 b => .ok (.Vbool (a != b))
    | o, v1, v2 => base.sem_sop2 o v1 v2
  sem_opN := base.sem_opN

theorem u64OpSem_wordOfInt (base : OpSem) : OpWordOfInt (u64OpSem base) := fun _ => rfl

theorem u64OpSem_neq (base : OpSem) : OpWordNeq (u64OpSem base) := fun _ _ => rfl

/-- The mirror function `copy(u8[n] r) -> u8[n] { return r; }`. -/
def copyFunDef (n : Nat) : FunDef :=
  { tyin := [.aarr .U8 n], params := [{ v_var := mArrVar "r" n }], body := [],
    tyout := [.aarr .U8 n], rets := [{ v_var := mArrVar "r" n }] }

/-- The mirror program holding `copyFunDef n` under the name `f`. -/
def copyProg (f : String) (n : Nat) : Prog :=
  { pFuncs := [({ name := f }, copyFunDef n)], pGlobs := [] }

/-- The call `d = f(a)` to a function returning its array argument, with `d` and `a` of
    the tower type `t`: `corresTrans_call` applies to the environment whose `f` returns its
    first argument and to the mirror program `copyProg f`. -/
theorem corresTrans_call_copy (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (sid : AScopeId)
    (f d a : String) (t : TowerType) :
    CorresTrans (SyscallState := SyscallState) (Mem := Mem) aS opS gd
      (copyProg f t.storageBytes)
      (pureLeafEnv (fun _ => some (fun vs =>
        [⟨.sarr t.storageBytes, callResultArr t.storageBytes (fun _ => 0) vs⟩])))
      sid (fun _ => True)
      (toJasminCmd (.RCall f { locVar := d, locSrc := t } [{ locVar := a, locSrc := t }]))
      (mirrorCallCmd f { locVar := d, locSrc := t } [{ locVar := a, locSrc := t }])
      (fun heap => setA heap sid d t.storageBytes (getA heap sid a t.storageBytes)) := by
  have h := corresTrans_call (SyscallState := SyscallState) (Mem := Mem) (aS := aS) opS gd
    (copyProg f t.storageBytes) sid
    (fun _ => some (fun vs => [⟨.sarr t.storageBytes, callResultArr t.storageBytes (fun _ => 0) vs⟩]))
    f { locVar := d, locSrc := t } [{ locVar := a, locSrc := t }]
    (callResultArr t.storageBytes (fun _ => 0)) rfl (copyFunDef t.storageBytes)
    (by simp [getFunDef, copyProg]) [{ v_var := mArrVar "r" t.storageBytes }]
    { v_var := mArrVar "r" t.storageBytes } rfl rfl rfl
    (by intro pa hpa; simp at hpa; subst hpa; rfl) rfl rfl
    (fun scs mem heap => ⟨_, .Eskip _, by
      simp [calleeParamArrs, paramVmA, callArgVals, callResultArr, Vm.get, Vm.set, ArrArg.value]⟩)
  simpa [callArgVals, callResultArr] using h

/-- The mirror function `swap(u8[n] p, u8[n] q) -> u8[n], u8[n] { return q, p; }`. -/
def swapFunDef (n : Nat) : FunDef :=
  { tyin := [.aarr .U8 n, .aarr .U8 n],
    params := [{ v_var := mArrVar "p" n }, { v_var := mArrVar "q" n }], body := [],
    tyout := [.aarr .U8 n, .aarr .U8 n],
    rets := [{ v_var := mArrVar "q" n }, { v_var := mArrVar "p" n }] }

/-- The mirror program holding `swapFunDef n` under the name `f`. -/
def swapProg (f : String) (n : Nat) : Prog :=
  { pFuncs := [({ name := f }, swapFunDef n)], pGlobs := [] }

/-- The outputs of a swap of two arrays of tower type `t`: the second argument value to
    `d1` and the first to `d2`. -/
def swapOuts (t : TowerType) (d1 d2 : String) (vs : List TypedValue) : List CallOut :=
  [⟨{ locVar := d1, locSrc := t }, callResultArr t.storageBytes (fun _ => 0) (vs.drop 1)⟩,
   ⟨{ locVar := d2, locSrc := t }, callResultArr t.storageBytes (fun _ => 0) vs⟩]

/-- The call `d1, d2 = f(a1, a2)` to a function returning its arguments swapped, all of
    the tower type `t`: `corresTrans_callN` applies to the environment whose `f` returns
    `swapOuts` and to the mirror program `swapProg f`. -/
theorem corresTrans_callN_swap (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (sid : AScopeId)
    (f d1 d2 a1 a2 : String) (t : TowerType) :
    CorresTrans (SyscallState := SyscallState) (Mem := Mem) aS opS gd
      (swapProg f t.storageBytes)
      (pureLeafEnv (fun _ => some (fun vs => (swapOuts t d1 d2 vs).map CallOut.typed)))
      sid (fun _ => True)
      (toJasminCmd (.RCallN f [{ locVar := d1, locSrc := t }, { locVar := d2, locSrc := t }]
        [{ locVar := a1, locSrc := t }, { locVar := a2, locSrc := t }]))
      (mirrorCallNCmd f [{ locVar := d1, locSrc := t }, { locVar := d2, locSrc := t }]
        [{ locVar := a1, locSrc := t }, { locVar := a2, locSrc := t }])
      (fun heap => setA (setA heap sid d1 t.storageBytes (getA heap sid a2 t.storageBytes))
        sid d2 t.storageBytes (getA heap sid a1 t.storageBytes)) := by
  have h := corresTrans_callN (SyscallState := SyscallState) (Mem := Mem) (aS := aS) opS gd
    (swapProg f t.storageBytes) sid
    (fun _ => some (fun vs => (swapOuts t d1 d2 vs).map CallOut.typed))
    f [{ locVar := d1, locSrc := t }, { locVar := d2, locSrc := t }]
    [{ locVar := a1, locSrc := t }, { locVar := a2, locSrc := t }]
    (swapOuts t d1 d2) (fun _ => rfl) rfl (swapFunDef t.storageBytes)
    (by simp [getFunDef, swapProg])
    [{ v_var := mArrVar "p" t.storageBytes }, { v_var := mArrVar "q" t.storageBytes }]
    [{ v_var := mArrVar "q" t.storageBytes }, { v_var := mArrVar "p" t.storageBytes }]
    rfl rfl rfl rfl
    (by
      intro pa hpa
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.mem_nil_iff,
        or_false] at hpa
      rcases hpa with rfl | rfl <;> rfl)
    rfl rfl
    (fun scs mem heap => ⟨_, .Eskip _, by
      intro ro hro
      simp only [swapOuts, List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
        List.mem_nil_iff, or_false] at hro
      rcases hro with rfl | rfl <;>
        simp [calleeParamArrs, paramVmA, callArgVals, callResultArr, Vm.get, Vm.set,
          ArrArg.value, mArrVar]⟩)
  simpa [callArgVals, callResultArr, writeOuts, swapOuts] using h

/-! ## §8. Worked witnesses

Each witness is a small `LowCT` program whose lowered command is translated to the
mirror and run there by the rules above; the final register or array values are read off
the state relation. -/

/-- The program `let x = 0u64; y := 5`. -/
def letZeroSetProg : LowCT := .RLetU64Zero "x" (.RScalarSet "y" 5)

/-- **Witness for `RLetU64Zero`.** The mirror image of `letZeroSetProg` runs under
    `execCmd` to a state with `x = 0` and `y = 5`. -/
theorem letZeroSetProg_mirror_exec (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)
    (env : TransEnv) (sid : AScopeId) (hop1 : OpWordOfInt opS)
    (s : Estate SyscallState Mem) (heap : AHeap) (hSR : MirrorHeapCorr sid s heap) :
    ∃ c' s' fuel, translateCmdExt (toJasminCmd letZeroSetProg) = some c' ∧
      execCmd aS opS gd fuel s c' prog = .ok s' ∧
      (s'.evm).get (mWordVar "x") = vW 0 ∧ (s'.evm).get (mWordVar "y") = vW 5 := by
  have hS := corresTrans_append
    (corresTrans_scalarSet (SyscallState := SyscallState) (Mem := Mem) aS opS gd prog env sid
      "x" 0 hop1)
    (corresTrans_scalarSet (SyscallState := SyscallState) (Mem := Mem) aS opS gd prog env sid
      "y" 5 hop1)
    (fun _ _ => trivial)
  obtain ⟨s', fuel, hrun, hSR'⟩ := corresSem_exec _ hS.2 s heap hSR trivial
  refine ⟨_, s', fuel, rfl, hrun, ?_, ?_⟩
  · rw [hSR'.1 "x", getW_setW_other _ _ _ _ _ (by decide), getW_setW_same]
    rfl
  · rw [hSR'.1 "y", getW_setW_same]
    rfl

/-- The program `while (e ≠ 0) { e := 0 }`. -/
def whileClearProg : LowCT := .RWhileNz "e" (.RScalarSet "e" 0)

/-- **Witness for `RWhileNz`.** The mirror image of `whileClearProg` runs under `execCmd`
    to a state with `e = 0`, from every related heap: the loop iterates once when `e` is
    nonzero and not at all otherwise. -/
theorem whileClearProg_mirror_exec (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)
    (env : TransEnv) (sid : AScopeId) (hop1 : OpWordOfInt opS) (hop2 : OpWordNeq opS)
    (s : Estate SyscallState Mem) (heap : AHeap) (hSR : MirrorHeapCorr sid s heap) :
    ∃ c' s' fuel, translateCmdExt (toJasminCmd whileClearProg) = some c' ∧
      execCmd aS opS gd fuel s c' prog = .ok s' ∧ (s'.evm).get (mWordVar "e") = vW 0 := by
  have hcount : ∀ heap : AHeap,
      (∀ j < (if getW heap sid "e" = 0 then 0 else 1),
        getW (iterFold (fun heap => setW heap sid "e" (BitVec.ofNat 64 0)) j heap) sid "e" ≠ 0) ∧
      getW (iterFold (fun heap => setW heap sid "e" (BitVec.ofNat 64 0))
        (if getW heap sid "e" = 0 then 0 else 1) heap) sid "e" = 0 := by
    intro heap
    by_cases h : getW heap sid "e" = 0
    · rw [if_pos h]
      exact ⟨fun j hj => absurd hj (Nat.not_lt_zero j), h⟩
    · rw [if_neg h]
      refine ⟨fun j hj => ?_, ?_⟩
      · obtain rfl : j = 0 := by omega
        exact h
      · rw [iterFold_succ, iterFold_zero, getW_setW_same]
        rfl
  obtain ⟨hc', hrun⟩ := toJasminCmd_whileNz_mirror_exec (aS := aS) (opS := opS) (gd := gd)
    (prog := prog) env sid hop1 hop2 "e" (.RScalarSet "e" 0)
    (b' := [.MkI () (.Cassgn (.Lvar { v_var := mWordVar "e" }) .AT_none (.aword .U64)
      (.Papp1 (.Oword_of_int .U64) (.Pconst 0)))]) rfl
    (corresTrans_scalarSet (SyscallState := SyscallState) (Mem := Mem) aS opS gd prog env sid
      "e" 0 hop1) _ hcount
  obtain ⟨s', fuel, hrun', hSR'⟩ := hrun s heap hSR
  refine ⟨_, s', fuel, hc', hrun', ?_⟩
  rw [hSR'.1 "e", (hcount heap).2]

/-- The program `c = clone(a); d = f(a)` over the tower type `t`. -/
def cloneCallProg (f : String) (t : TowerType) : LowCT :=
  .RCloneCall "c" t { locVar := "a", locSrc := t } f { locVar := "d", locSrc := t }
    [{ locVar := "a", locSrc := t }]

/-- **Witness for `RCloneCall`.** In `copyProg f`, the mirror image of `cloneCallProg f t`
    runs under `execCmd` to a state holding the array of `a` at both `c` and `d`. -/
theorem cloneCallProg_mirror_exec (aS : AsmSem) (opS : OpSem) (gd : GlobDecls)
    (sid : AScopeId) (hclone : AsmClone aS) (f : String) (t : TowerType)
    (s : Estate SyscallState Mem) (heap : AHeap) (hSR : MirrorHeapCorr sid s heap) :
    ∃ c' s' fuel, translateCmdExt (toJasminCmd (cloneCallProg f t)) = some c' ∧
      execCmd aS opS gd fuel s c' (copyProg f t.storageBytes) = .ok s' ∧
      (s'.evm).get (mArrVar "c" t.storageBytes) = vA _ (getA heap sid "a" t.storageBytes) ∧
      (s'.evm).get (mArrVar "d" t.storageBytes) = vA _ (getA heap sid "a" t.storageBytes) := by
  have hS := corresTrans_append
    (corresTrans_cloneTower (SyscallState := SyscallState) (Mem := Mem) opS gd
      (copyProg f t.storageBytes)
      (pureLeafEnv (fun _ => some (fun vs =>
        [⟨.sarr t.storageBytes, callResultArr t.storageBytes (fun _ => 0) vs⟩])))
      sid hclone "c" "a" t)
    (corresTrans_call_copy (SyscallState := SyscallState) (Mem := Mem) aS opS gd sid f "d" "a" t)
    (fun _ _ => trivial)
  obtain ⟨s', fuel, hrun, hSR'⟩ := corresSem_exec _ hS.2 s heap hSR trivial
  refine ⟨_, s', fuel, ?_, hrun, ?_, ?_⟩
  · exact translateCmdExt_append_some (translateCmdExt_cloneTower "c" t "a")
      (translateCmdExt_call f { locVar := "d", locSrc := t } [{ locVar := "a", locSrc := t }])
  · rw [hSR'.2 "c", getA_setA_other _ _ _ _ _ _ _ (fun h => absurd h.1 (by decide)),
      getA_setA_same]
  · rw [hSR'.2 "d", getA_setA_same, getA_setA_other _ _ _ _ _ _ _ (fun h => absurd h.1 (by decide))]

/-- The program `d1, d2 = f(a1, a2)` over the tower type `t`. -/
def swapCallProg (f : String) (t : TowerType) : LowCT :=
  .RCallN f [{ locVar := "d1", locSrc := t }, { locVar := "d2", locSrc := t }]
    [{ locVar := "a1", locSrc := t }, { locVar := "a2", locSrc := t }]

/-- **Witness for `RCallN`.** In `swapProg f`, the mirror image of `swapCallProg f t` runs
    under `execCmd` to a state holding the array of `a2` at `d1` and the array of `a1` at
    `d2`. -/
theorem swapCallProg_mirror_exec (aS : AsmSem) (opS : OpSem) (gd : GlobDecls)
    (sid : AScopeId) (f : String) (t : TowerType)
    (s : Estate SyscallState Mem) (heap : AHeap) (hSR : MirrorHeapCorr sid s heap) :
    ∃ c' s' fuel, translateCmdExt (toJasminCmd (swapCallProg f t)) = some c' ∧
      execCmd aS opS gd fuel s c' (swapProg f t.storageBytes) = .ok s' ∧
      (s'.evm).get (mArrVar "d1" t.storageBytes) = vA _ (getA heap sid "a2" t.storageBytes) ∧
      (s'.evm).get (mArrVar "d2" t.storageBytes) = vA _ (getA heap sid "a1" t.storageBytes) := by
  have hS := corresTrans_callN_swap (SyscallState := SyscallState) (Mem := Mem) aS opS gd sid
    f "d1" "d2" "a1" "a2" t
  obtain ⟨s', fuel, hrun, hSR'⟩ := corresSem_exec _ hS.2 s heap hSR trivial
  refine ⟨_, s', fuel, translateCmdExt_callN f _ _, hrun, ?_, ?_⟩
  · rw [hSR'.2 "d1", getA_setA_other _ _ _ _ _ _ _ (fun h => absurd h.1 (by decide)),
      getA_setA_same]
  · rw [hSR'.2 "d2", getA_setA_same]

end CatCrypt.Crypto.SecureCompilation.VIR.LowCTMirrorCorres
