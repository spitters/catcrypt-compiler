/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsaCallX86
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsaStackFrame

/-!
# The region export at the ABI: checker, entry, result and return

Facts about the region export `exportR` of `ExportRegions` that a caller at the System V
entry uses.

## Main definitions

* `regVar?`, `bindMemNB`, `regionExportableB`: the first register variable of a context, a
  Boolean test of `BindMemN` and a Boolean test of `RegionExportable`.

## Main statements

* `bindMemNB_sound`, `regionExportableB_sound`: the tests are sound.
* `exportRBody_eq_map`, `exportRLfundef_body`: the wire body of `exportRBody` and of
  `exportRLfundef` is the wire projection of the typed code followed by a return.
* `exportR_lsemFuelMemF_abi`: from an ABI entry state the exported code halts at the counter
  after its last instruction in a state that agrees with the returned operands.
* `ResAgrees.getW_single`, `ResAgrees.decodeArrM_single`: the reading of a single register
  result and of a single array result off a state that agrees with the returned operands.
* `exportR_ret_steps`: the run of the exported code followed by a return, on the
  instruction set with calls, from an entry state with a return address on the stack to
  the return address, for code that does not name the stack pointer.
* `ResAgrees.retState_spFrame`: the agreement with the returned operands holds in the state
  after the return.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond (decodeArrM)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (IsaData isCall)
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (x86Data)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment (scalarMemNB
  scalarMemNB_sound)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf AbiEntryM
  storeAgreesM_of_abi)
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCall

/-! ## 1. The Boolean test of `RegionExportable` -/

/-- The first register variable of a context, with its width. -/
def regVar? : (Γ : Ctxt jasminDialect) → Option (Σ w : Nat, Ctxt.Var Γ (JasminTy.reg w))
  | [] => none
  | .reg w :: _ => some ⟨w, .here⟩
  | _ :: Γ => (regVar? Γ).map fun p => ⟨p.1, .there p.2⟩

/-- A Boolean test of `BindMemN`: the program that binds `e` and returns the first register
    variable in scope passes `scalarMemNB`. -/
def bindMemNB {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t) : Bool :=
  match regVar? (t :: Γ) with
  | some p => scalarMemNB (Com.var e (Com.ret p.2))
  | none => false

/-- The test `bindMemNB` is sound for `BindMemN`. -/
theorem bindMemNB_sound {Γ : Ctxt jasminDialect} {t : JasminTy} {e : Expr jasminDialect Γ t}
    (h : bindMemNB e = true) : BindMemN e := by
  unfold bindMemNB at h
  split at h
  · rename_i p _
    exact ⟨p.1, p.2, scalarMemNB_sound _ h⟩
  · cases h

/-- A Boolean test of `RegionExportable`, by the same recursion. -/
def regionExportableB : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    NFProg jasminDialect Γ ts → Bool
  | _, _, .ret _ => true
  | _, _, .var e k => bindMemNB e && regionExportableB k
  | _, _, .forLoop (cs := cs) _ _ body k =>
      cs.all isRegTy && regionExportableB body && regionExportableB k
  | _, _, .ifThenElse (rs := rs) _ thn els k =>
      rs.all isRegTy && regionExportableB thn && regionExportableB els && regionExportableB k
  | _, _, .whileLoop (cs := cs) _ body k =>
      cs.all isRegTy && regionExportableB body && regionExportableB k
  | _, _, .call _ _ _ => false

/-- **The test `regionExportableB` is sound for `RegionExportable`.** -/
theorem regionExportableB_sound {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : regionExportableB p = true) : RegionExportable p := by
  induction p with
  | ret vs => trivial
  | var e k ih =>
      simp only [regionExportableB, Bool.and_eq_true] at h
      exact ⟨bindMemNB_sound h.1, ih h.2⟩
  | forLoop count inits body k ihb ihk =>
      simp only [regionExportableB, Bool.and_eq_true] at h
      exact ⟨fun t ht => List.all_eq_true.mp h.1.1 t ht, ihb h.1.2, ihk h.2⟩
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [regionExportableB, Bool.and_eq_true] at h
      exact ⟨fun t ht => List.all_eq_true.mp h.1.1.1 t ht, iht h.1.1.2, ihe h.1.2, ihk h.2⟩
  | whileLoop inits body k ihb ihk =>
      simp only [regionExportableB, Bool.and_eq_true] at h
      exact ⟨fun t ht => List.all_eq_true.mp h.1.1 t ht, ihb h.1.2, ihk h.2⟩
  | call f args k _ => simp [regionExportableB] at h

/-! ## 2. The wire body -/

/-- The wire body of `exportRBody` is the wire projection of the typed code followed by a
    return with any tag. -/
theorem exportRBody_eq_map {fn : String} {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} {I : IsaData} {r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 I = some r) (tag : MemTag) :
    exportRBody fn p I
      = some ((r.code ++ [((LinstrR.Lret, tag) : LinstrRM)]).map
          fun i => (⟨0, i.1⟩ : Linstr)) := by
  simp only [exportRBody, hr, Option.map_some, List.map_append, List.map_cons, List.map_nil]

/-- The body of `exportRLfundef` is the wire body `exportRBody`. -/
theorem exportRLfundef_body (fn : String) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (I : IsaData) :
    (exportRLfundef fn p I).map (·.lfd_body) = exportRBody fn p I := by
  simp only [exportRLfundef, exportRBody, Option.map_map]
  rfl

/-! ## 3. Entry and result at the ABI -/

/-- **The run of a whole program from an ABI entry.** For a program of `RegionExportable`
    that denotes `v` at a valuation `V` a layout `σ` reads off an entry state `sa`, the
    exported code run by `lsemFuelMemF` from a flag-machine ABI entry of `sa` halts at
    every fuel from some bound on, at the counter after the last instruction, in a state
    that agrees with the returned operands at `v`. -/
theorem exportR_lsemFuelMemF_abi (fn : String) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (hp : RegionExportable p) (fuel : Nat)
    (V : Ctxt.Valuation Γ) (v : Ctxt.Valuation (d := jasminDialect) ts)
    (hden : p.denote fuel V = some v) (σ : AbiLayout) (sa : AState) (b0 : LstateM)
    (zf : Bool) (hV : AbiValOf σ sa V) (hb : AbiEntryM σ sa b0) :
    ∃ r, exportR Γ.length fn p Γ.length 0 = some r ∧ ∃ (k : Nat) (t : LstateMF),
      (∀ j, lsemFuelMemF (singletonProgM fn r.code) (k + j)
        { prog := { base := b0, lfn := fn }, zf := zf } = some t)
      ∧ atPc (singletonProgM fn r.code) r.code.length t
      ∧ ResAgrees Γ.length r.depth t.prog.base r.res v
      ∧ RegionFrame Γ.length 0 b0 t.prog.base :=
  exportR_lsemFuelMemF fn hp fuel V v hden b0 zf hb.pc (storeAgreesM_of_abi hV hb)

/-- **The reading of a single register result.** A state that agrees with the returned
    operands of a program with one result of type `reg w` has one returned operand, and
    the register it names holds the result at width `w`. -/
theorem ResAgrees.getW_single {nArgs D : Nat} {s : LstateM} {w : Nat} {ops : List LOperand}
    {v : Ctxt.Valuation (d := jasminDialect) [JasminTy.reg w]}
    (h : ResAgrees nArgs D s ops v) :
    ∃ op, ops = [op] ∧ s.reg.getW (operandName op) w
      = some (Ctxt.Var.lookup (d := jasminDialect) (Γ := [JasminTy.reg w])
          (t := JasminTy.reg w) .here v) := by
  obtain ⟨Δ, W, vs, -, hag, rfl, rfl⟩ := h
  cases vs with
  | cons x rest =>
      cases rest
      refine ⟨_, rfl, ?_⟩
      rw [← evalOperandN_resolveVar]
      exact hag.reg x

/-- **The reading of a single array result.** A state that agrees with the returned
    operands of a program with one result of type `stackArr w n` has one returned operand,
    and the array it names decodes to the result. -/
theorem ResAgrees.decodeArrM_single {nArgs D : Nat} {s : LstateM} {w n : Nat}
    {ops : List LOperand} {v : Ctxt.Valuation (d := jasminDialect) [JasminTy.stackArr w n]}
    (h : ResAgrees nArgs D s ops v) :
    ∃ op, ops = [op] ∧ decodeArrM s (operandName op) w n
      = some (Ctxt.Var.lookup (d := jasminDialect) (Γ := [JasminTy.stackArr w n])
          (t := JasminTy.stackArr w n) .here v) := by
  obtain ⟨Δ, W, vs, -, hag, rfl, rfl⟩ := h
  cases vs with
  | cons x rest =>
      cases rest
      exact ⟨_, rfl, hag.arr x⟩

/-! ## 4. The return -/

/-- **The run of the exported code followed by a return.** Let `p` be a program of
    `RegionExportable` with the export `r` whose code does not name `RSP` (`spFreeBodyB`),
    and let `p` denote `v` at `V`. From an entry state at the counter `0` whose store agrees
    with `V`, with the stack pointer `RSP` holding `sp - 8` and the memory cell it addresses
    holding the word of a counter `ra` below `2 ^ 64`, the instruction set with calls makes
    on the code followed by `Lret` a run to the counter `ra` with `RSP` holding `sp`. The
    end state is that of the run without the stack pointer, `t`, with the stack pointer and
    its cell replaced; `t` agrees with the returned operands at `v`. -/
theorem exportR_ret_steps (fn : String) (tag : MemTag) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} {p : NFProg jasminDialect Γ ts} (hp : RegionExportable p)
    {r : Exported} (hr : exportR Γ.length fn p Γ.length 0 = some r)
    (hsp : spFreeBodyB "RSP" r.code = true) (fuel : Nat)
    (V : Ctxt.Valuation Γ) (v : Ctxt.Valuation (d := jasminDialect) ts)
    (hden : p.denote fuel V = some v) (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0)
    (hag : StoreAgreesM Γ.length Γ.length b0 V) (sp : BitVec 64) (ra : Nat)
    (hra : ra < 2 ^ 64) :
    ∃ (n : Nat) (t : LstateMF),
      Steps x86Isa.withCalls (singletonProgM fn (r.code ++ [(.Lret, tag)])) (n + 1)
        (spFrame "RSP" (sp - 8) (BitVec.ofNat 64 ra)
          { prog := { base := b0, lfn := fn }, zf := zf })
        (retState "RSP" sp ra (spFrame "RSP" (sp - 8) (BitVec.ofNat 64 ra) t))
      ∧ atPc (singletonProgM fn (r.code ++ [(.Lret, tag)])) ra
        (retState "RSP" sp ra (spFrame "RSP" (sp - 8) (BitVec.ofNat 64 ra) t))
      ∧ ResAgrees Γ.length r.depth t.prog.base r.res v
      ∧ RegionFrame Γ.length 0 b0 t.prog.base := by
  obtain ⟨k, t, hrun, hat, hres, hfr⟩ := exportRSim_lsemFuelMemF (exportR_sim Γ.length fn hp)
    hr rfl le_rfl fuel V v hden b0 zf hpc hag
  have hrun0 := hrun 0
  rw [← X86Backend.X86Isa.x86Isa_lsemFuelMemF] at hrun0
  have hrun' : x86Isa.lsemFuelMemF (singletonProgM fn r.code) (k + 0)
      (spFrame "RSP" (sp - 8) (BitVec.ofNat 64 ra)
        { prog := { base := b0, lfn := fn }, zf := zf })
      = some (spFrame "RSP" (sp - 8) (BitVec.ofNat 64 ra) t) := by
    rw [x86_lsemFuelMemF_spFrame (P := singletonProgM fn r.code) (spFree_of_spFreeBodyB hsp),
      hrun0]
    rfl
  obtain ⟨n, -, hsteps, hatr⟩ := x86_steps_snoc_ret (tag := tag)
    (exportR_noCall _ _ x86Data_guardsNoCall p _ _ _ hr) hrun' ⟨hat.1, hat.2⟩
    (LstateN.getW_setReg_same _ _ _)
    (show (spM "RSP" (sp - 8) (BitVec.ofNat 64 ra) t.prog.base).lmem "RSP" (sp - 8).toInt
        = BitVec.ofNat 64 ra by simp [spM, LstateM.storeMemC]) hra
  exact ⟨n, t, hsteps, hatr, hres, hfr⟩

/-! ## 5. The result after the return -/

/-- No register `regName d` is the stack pointer. -/
theorem regName_ne_rsp (d : Nat) : regName d ≠ "RSP" := by
  intro h
  have := congrArg String.toList h
  simp [regName] at this

/-- No argument name is the stack pointer. -/
theorem argName_ne_rsp (j : Nat) : argName j ≠ "RSP" := by
  intro h
  have := congrArg String.toList h
  simp [argName] at this

/-- The name of an in-scope variable is not the stack pointer. -/
theorem resolveVar_operandName_ne_rsp {curDepth nArgs : Nat} {Γ : Ctxt jasminDialect}
    {τ : JasminTy} (v : Ctxt.Var Γ τ) :
    operandName (resolveVar curDepth nArgs argName (fun _ => none) v) ≠ "RSP" := by
  simp only [resolveVar, operandName]
  by_cases hsa : curDepth - 1 - varIndex v < nArgs
  · simp only [hsa, if_true]
    exact argName_ne_rsp _
  · simp only [hsa, if_false]
    exact regName_ne_rsp _

/-- The state after the return reads as the state before the replacement of the stack
    pointer at every register other than `RSP`. -/
theorem getW_retState_spFrame (t : LstateMF) (v0 w0 sp : BitVec 64) (ra : Nat) {r : String}
    (w : Nat) (hr : r ≠ "RSP") :
    (retState "RSP" sp ra (spFrame "RSP" v0 w0 t)).prog.base.reg.getW r w
      = t.prog.base.reg.getW r w := by
  have hl : (retState "RSP" sp ra (spFrame "RSP" v0 w0 t)).prog.base.reg.lvm r
      = t.prog.base.reg.lvm r := by
    simp [retState, spFrame, spM, LstateM.setReg, LstateM.setLpc, LstateM.storeMemC,
      LstateN.setReg, hr]
  unfold LstateN.getW
  rw [hl]

/-- The state after the return reads as the state before the replacement of the stack
    pointer at every array. -/
theorem getArr_retState_spFrame (t : LstateMF) (v0 w0 sp : BitVec 64) (ra : Nat) (r : String)
    (w n : Nat) :
    (retState "RSP" sp ra (spFrame "RSP" v0 w0 t)).prog.base.getArr r w n
      = t.prog.base.getArr r w n := by
  simp [retState, spFrame, spM, getArr_setLpc, getArr_storeMemC]

/-- **The agreement with the returned operands holds after the return.** The replacement
    of the stack pointer and its cell and the return step keep the agreement with the
    returned operands. -/
theorem ResAgrees.retState_spFrame {nArgs D : Nat} {t : LstateMF} {ts : List JasminTy}
    {ops : List LOperand} {v : Ctxt.Valuation (d := jasminDialect) ts}
    (h : ResAgrees nArgs D t.prog.base ops v) (v0 w0 sp : BitVec 64) (ra : Nat) :
    ResAgrees nArgs D (retState "RSP" sp ra (spFrame "RSP" v0 w0 t)).prog.base ops v := by
  obtain ⟨Δ, W, vs, hΔ, hag, hops, hv⟩ := h
  refine ⟨Δ, W, vs, hΔ, ⟨fun {w'} x => ?_, fun {w' n} x => ?_⟩, hops, hv⟩
  · rw [evalOperandN_resolveVar,
      getW_retState_spFrame t v0 w0 sp ra w' (resolveVar_operandName_ne_rsp x),
      ← evalOperandN_resolveVar]
    exact hag.reg x
  · rw [getArr_retState_spFrame]
    exact hag.arr x

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
