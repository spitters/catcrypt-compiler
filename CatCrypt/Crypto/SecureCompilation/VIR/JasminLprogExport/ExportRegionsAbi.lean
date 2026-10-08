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
* `ResAgrees.retState_spFrame`: the agreement with the returned operands holds in the state
  after the return.
* `exportR_spFree`, `exportR_spFreeBodyB`: neither the code nor the returned operands of
  the export of a program of `RegionExportable` name the stack pointer `RSP`.
* `exportR_ret_steps`: the run of the exported code followed by a return, on the
  instruction set with calls, from an entry state with a return address on the stack to
  the return address.
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
  | _, _, .forLoop _ _ body k => regionExportableB body && regionExportableB k
  | _, _, .ifThenElse (rs := rs) _ thn els k =>
      rs.all isRegTy && regionExportableB thn && regionExportableB els && regionExportableB k
  | _, _, .whileLoop (cs := cs) _ body k =>
      cs.all isRegTy && regionExportableB body && regionExportableB k
  | _, _, .call (as := as) (rs := rs) _ _ k => wordSig as rs && regionExportableB k

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
      exact ⟨ihb h.1, ihk h.2⟩
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [regionExportableB, Bool.and_eq_true] at h
      exact ⟨fun t ht => List.all_eq_true.mp h.1.1.1 t ht, iht h.1.1.2, ihe h.1.2, ihk h.2⟩
  | whileLoop inits body k ihb ihk =>
      simp only [regionExportableB, Bool.and_eq_true] at h
      exact ⟨fun t ht => List.all_eq_true.mp h.1.1 t ht, ihb h.1.2, ihk h.2⟩
  | call f args k ih =>
      simp only [regionExportableB, Bool.and_eq_true] at h
      exact ⟨h.1, ih h.2⟩

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

/-! ## 4. The result after the return -/

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

/-! ## 5. The export does not name the stack pointer -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrCongr (cellBase)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (cellParts?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagArrLoop (OpPlain ComOpsPlain
  scalarMemN_comOpsPlain)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift (shiftLinstr)

/-- A register whose name starts with a character other than `m` and `R` does not name
    `RSP`: it is neither `RSP` nor a cell name `mem.RSP.<off>`. -/
theorem opSpB_reg_of_head {r : String} {c : Char} (hr : r.toList.head? = some c)
    (hm : c ≠ 'm') (hR : c ≠ 'R') : opSpB "RSP" (.reg r) = false := by
  have h1 : r ≠ "RSP" := by
    rintro rfl
    exact hR (Option.some.inj hr).symm
  have h2 : cellParts? r = none := by
    unfold cellParts?
    rw [if_neg]
    cases hl : r.toList with
    | nil => simp [hasPrefix, hl]
    | cons a tl =>
        rw [hl] at hr
        obtain rfl : a = c := Option.some.inj hr
        simp [hasPrefix, hl, Ne.symm hm]
  simp [opSpB, cellBase, h1, h2]

/-- The register `regName d` does not name `RSP`. -/
theorem opSpB_regName (d : Nat) : opSpB "RSP" (.reg (regName d)) = false :=
  opSpB_reg_of_head (c := 'r') (by simp [regName]) (by decide) (by decide)

/-- The argument register `argName j` does not name `RSP`. -/
theorem opSpB_argName (j : Nat) : opSpB "RSP" (.reg (argName j)) = false :=
  opSpB_reg_of_head (c := 'a') (by simp [argName]) (by decide) (by decide)

/-- The loop counter `loopCtr n` does not name `RSP`. -/
theorem opSpB_loopCtr (n : Nat) : opSpB "RSP" (.reg (loopCtr n)) = false :=
  opSpB_reg_of_head (c := 'L') (by simp [loopCtr]) (by decide) (by decide)

/-- The operand of an in-scope variable does not name `RSP`. -/
theorem opSpB_resolveVar {curDepth nArgs : Nat} {Γ : Ctxt jasminDialect} {τ : JasminTy}
    (v : Ctxt.Var Γ τ) :
    opSpB "RSP" (resolveVar curDepth nArgs argName (fun _ => none) v) = false := by
  simp only [resolveVar]
  split
  · exact opSpB_argName _
  · exact opSpB_regName _

/-- The operands of a vector of in-scope variables do not name `RSP`. -/
theorem opSpB_exprArgsHV {Γ : Ctxt jasminDialect} (cd nArgs : Nat) :
    ∀ {ts : List JasminTy} (vs : HVector (fun ty => Ctxt.Var Γ ty) ts),
      ∀ o ∈ exprArgsHV cd nArgs argName (fun _ => none) vs, opSpB "RSP" o = false
  | [], .nil, o, h => by simp [exprArgsHV] at h
  | _ :: _, .cons v rest, o, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact opSpB_resolveVar v
      · exact opSpB_exprArgsHV cd nArgs rest o h'

/-- The source operands of a binding do not name `RSP`. -/
theorem opSpB_exprArgs {curDepth nArgs : Nat} {Γ : Ctxt jasminDialect} {τ : JasminTy}
    (e : Expr jasminDialect Γ τ) :
    ∀ o ∈ exprArgs curDepth nArgs argName (fun _ => none) e, opSpB "RSP" o = false := by
  have go : ∀ {tys : List JasminTy} (hv : HVector (fun ty => Ctxt.Var Γ ty) tys)
      (o : LOperand), o ∈ exprArgs.go curDepth nArgs argName (fun _ => none) hv →
      opSpB "RSP" o = false := by
    intro tys hv
    induction hv with
    | nil =>
        intro o ho
        rw [show exprArgs.go curDepth nArgs argName (fun _ => none)
            (HVector.nil (f := fun ty => Ctxt.Var Γ ty)) = ([] : List LOperand) from rfl] at ho
        simp at ho
    | cons v rest ih =>
        intro o ho
        have hgo : exprArgs.go curDepth nArgs argName (fun _ => none) (HVector.cons v rest)
            = resolveVar curDepth nArgs argName (fun _ => none) v
              :: exprArgs.go curDepth nArgs argName (fun _ => none) rest := rfl
        rw [hgo, List.mem_cons] at ho
        rcases ho with rfl | ho
        · exact opSpB_resolveVar v
        · exact ih o ho
  exact fun o ho => go e.args o ho

/-- The registers of a carried block do not name `RSP`. -/
theorem opSpB_carriedRegs {d nCar : Nat} {r : String} (hr : r ∈ carriedRegs d nCar) :
    opSpB "RSP" (.reg r) = false := by
  obtain ⟨j, -, rfl⟩ := mem_carriedRegs.mp hr
  exact opSpB_regName _

/-- An `Lopn` with one register destination passes `spFreeB` when neither the destination
    nor a source names `RSP`. -/
theorem spFreeB_lopn {dst : String} {m : String} {ss : List LOperand}
    (hd : opSpB "RSP" (.reg dst) = false) (hs : ∀ o ∈ ss, opSpB "RSP" o = false) :
    spFreeB "RSP" (.Lopn [.reg dst] m ss) = true := by
  have : ss.any (opSpB "RSP") = false := List.any_eq_false.mpr fun o ho => by simp [hs o ho]
  simp [spFreeB, hd, this]

/-- The operands of a pair of a register that does not name `RSP` and an immediate do not
    name `RSP`. -/
theorem opSpB_pair_imm {r : String} (hr : opSpB "RSP" (.reg r) = false) (k : Nat) :
    ∀ o ∈ [LOperand.reg r, .imm k], opSpB "RSP" o = false := by
  intro o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · exact hr
  · rfl

/-- A move passes `spFreeB` when neither operand names `RSP`. -/
theorem spFreeB_movI {dst : String} {src : LOperand} (hd : opSpB "RSP" (.reg dst) = false)
    (hs : opSpB "RSP" src = false) : spFreeB "RSP" (movI dst src).fst = true :=
  spFreeB_lopn hd (by simpa using hs)

/-- An indexed element does not name `RSP` when neither its base nor its index does. -/
theorem opSpB_arrIdx {b i : String} (k : Nat) (hb : opSpB "RSP" (.reg b) = false)
    (hi : opSpB "RSP" (.reg i) = false) : opSpB "RSP" (.arrIdx b i k) = false := by
  simp only [opSpB, Bool.or_eq_false_iff] at hb hi ⊢
  exact ⟨hb.1, hi.1⟩

/-- The instruction of an op of the stack-memory fragment passes `spFreeB` when neither
    its destination nor a source names `RSP`. Belongs beside `opToLinstrR_plain` in
    `JasminLsemMemFlagArrLoop`. -/
theorem spFreeB_opToLinstrR (op : JasminOp) (hop : OpPlain op) {dst : String}
    {srcs : List LOperand} (hd : opSpB "RSP" (.reg dst) = false)
    (hs : ∀ o ∈ srcs, opSpB "RSP" o = false) :
    spFreeB "RSP" (opToLinstrR op dst srcs) = true := by
  cases op <;> simp only [OpPlain] at hop
  case regConst w k => exact spFreeB_lopn hd (by simp [opSpB])
  case castW w w' =>
    simp only [opToLinstrR]
    split <;> exact spFreeB_lopn hd hs
  case stackLoad w k =>
    simp only [opToLinstrR]
    split
    · refine spFreeB_lopn hd fun o ho => ?_
      obtain rfl := List.mem_singleton.mp ho
      exact opSpB_arrIdx _ (hs _ (by simp)) (hs _ (by simp))
    · exact spFreeB_lopn hd hs
  case stackStore w k =>
    simp only [opToLinstrR]
    split
    · refine spFreeB_lopn hd fun o ho => ?_
      rcases List.mem_cons.mp ho with rfl | ho
      · exact opSpB_arrIdx _ (hs _ (by simp)) (hs _ (by simp))
      · obtain rfl := List.mem_singleton.mp ho
        exact hs _ (by simp)
    · exact spFreeB_lopn hd hs
  all_goals exact spFreeB_lopn hd hs

/-- The structured shift instruction passes `spFreeB` when neither its destination nor
    its source names `RSP`. -/
theorem spFreeB_shiftLinstr (mn : String) (w : Nat) {dst : String} {s : LOperand} (k : Nat)
    (hd : opSpB "RSP" (.reg dst) = false) (hs : opSpB "RSP" s = false) :
    spFreeB "RSP" (shiftLinstr mn w dst s k) = true :=
  spFreeB_lopn hd fun o ho => by
    rcases List.mem_cons.mp ho with rfl | ho
    · exact hs
    · obtain rfl := List.mem_singleton.mp ho
      rfl

/-- The instruction of a binding of the stack-memory fragment does not name `RSP`. -/
theorem bindOps_spFree (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    {e : Expr jasminDialect Γ t} (he : BindMemN e) (d : Nat) :
    ∀ i ∈ bindOps nArgs e d, spFreeB "RSP" i.fst = true := by
  obtain ⟨w, v, h⟩ := he
  have hop : OpPlain e.op := (scalarMemN_comOpsPlain h).1
  have hs := opSpB_exprArgs (curDepth := d) (nArgs := nArgs) e
  intro i hi
  simp only [bindOps, straightOpsMem, List.mem_cons, List.not_mem_nil, or_false] at hi
  subst hi
  generalize exprArgs d nArgs argName (fun _ => none) e = src at hs ⊢
  split
  · exact spFreeB_opToLinstrR _ hop (opSpB_regName _) hs
  · exact spFreeB_opToLinstrR _ hop (opSpB_regName _) hs
  · exact spFreeB_opToLinstrR _ hop (opSpB_regName _) hs
  · exact spFreeB_opToLinstrR _ hop (opSpB_regName _) hs
  · split
    · exact spFreeB_shiftLinstr _ _ _ (opSpB_regName _) (hs _ (by simp))
    · exact spFreeB_shiftLinstr _ _ _ (opSpB_regName _) (hs _ (by simp))
    · exact spFreeB_shiftLinstr _ _ _ (opSpB_regName _) (hs _ (by simp))
    · exact spFreeB_opToLinstrR _ hop (opSpB_regName _) hs

/-- The guards of an instruction set on a register that does not name `RSP` pass
    `spFreeB`. -/
structure GuardsSpFree (I : IsaData) : Prop where
  /-- The zero-trip guard does not name `RSP`. -/
  zeroTrip : ∀ (c : String) (t e : LLabel), opSpB "RSP" (.reg c) = false →
    ∀ i ∈ I.zeroTripGuard c t e, spFreeB "RSP" i = true
  /-- The back-edge guard does not name `RSP`. -/
  loop : ∀ (c : String) (t : LLabel), opSpB "RSP" (.reg c) = false →
    ∀ i ∈ I.loopGuard c t, spFreeB "RSP" i = true

/-- The guards of x86 satisfy `GuardsSpFree`. -/
theorem x86Data_guardsSpFree : GuardsSpFree x86Data where
  zeroTrip c t e hc i hi := by
    rw [X86Backend.TwoAddrLegalize.x86Data_zeroTripGuard] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact spFreeB_lopn hc (opSpB_pair_imm hc 0)
    · simp [spFreeB, opSpB_reg_of_head (r := "Z") (c := 'Z') rfl (by decide) (by decide)]
  loop c t hc i hi := by
    rw [X86Backend.TwoAddrLegalize.x86Data_loopGuard] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact spFreeB_lopn hc (opSpB_pair_imm hc 0)
    · simp [spFreeB, opSpB_reg_of_head (r := "NZ") (c := 'N') rfl (by decide) (by decide)]

/-- The seeds of a block of registers do not name `RSP` when neither a register nor an
    operand does. -/
theorem seedMoves_spFree {car : List String} {ops : List LOperand}
    (hc : ∀ r ∈ car, opSpB "RSP" (.reg r) = false) (ho : ∀ o ∈ ops, opSpB "RSP" o = false) :
    ∀ i ∈ seedMoves car ops, spFreeB "RSP" i.fst = true := fun i hi => by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hi
  obtain ⟨h1, h2⟩ := List.of_mem_zip hp
  exact spFreeB_movI (hc _ h1) (ho _ h2)

/-- A parallel assignment does not name `RSP` when neither a target nor an operand
    does. -/
theorem parMoves_spFree (D : Nat) {tgts : List String} {ops : List LOperand}
    (ht : ∀ r ∈ tgts, opSpB "RSP" (.reg r) = false) (ho : ∀ o ∈ ops, opSpB "RSP" o = false) :
    ∀ i ∈ parMoves D tgts ops, spFreeB "RSP" i.fst = true := by
  intro i hi
  simp only [parMoves, stageMoves, commitMoves, List.mem_append, List.mem_map] at hi
  rcases hi with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · exact spFreeB_movI (opSpB_regName _) (ho _ (List.fst_mem_of_mem_zipIdx hp))
  · exact spFreeB_movI (ht _ (List.fst_mem_of_mem_zipIdx hp)) (opSpB_regName _)

/-- The widening of a bit does not name `RSP` when none of its registers and its operand
    does. -/
theorem flagWord_spFree (I : IsaData) {r z : String} {op : LOperand}
    (hr : opSpB "RSP" (.reg r) = false) (hz : opSpB "RSP" (.reg z) = false)
    (ho : opSpB "RSP" op = false) : ∀ i ∈ flagWord I r z op, spFreeB "RSP" i.fst = true := by
  intro i hi
  cases op with
  | reg f =>
      simp only [flagWord] at hi
      cases hm : I.selectMnemonic with
      | none => simp [hm] at hi
      | some m =>
          simp only [hm, List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl | rfl
          · exact spFreeB_movI hr rfl
          · exact spFreeB_movI hz rfl
          · exact spFreeB_lopn hr (by simp [ho, hr, hz])
  | arr b k => simp only [flagWord, List.mem_singleton] at hi; subst hi; exact spFreeB_movI hr ho
  | imm v => simp only [flagWord, List.mem_singleton] at hi; subst hi; exact spFreeB_movI hr ho
  | arrIdx b k s =>
      simp only [flagWord, List.mem_singleton] at hi; subst hi; exact spFreeB_movI hr ho

/-- The moves of a block down one register do not name `RSP`. -/
theorem shiftMoves_spFree (d nCar : Nat) :
    ∀ i ∈ shiftMoves d nCar, spFreeB "RSP" i.fst = true := fun i hi => by
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hi
  exact spFreeB_movI (opSpB_regName _) (opSpB_regName _)

/-- The advance of a counted loop does not name `RSP` when neither of its registers
    does. -/
theorem advanceOps_spFree {idx ctr : String} (hi : opSpB "RSP" (.reg idx) = false)
    (hc : opSpB "RSP" (.reg ctr) = false) :
    ∀ i ∈ advanceOps idx ctr, spFreeB "RSP" i.fst = true := by
  intro i hmem
  simp only [advanceOps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · exact spFreeB_lopn hi (opSpB_pair_imm hi 1)
  · exact spFreeB_lopn hc (opSpB_pair_imm hc 1)

/-- The frame of a counted loop does not name `RSP` when its body and operands do not. -/
theorem forFrame_spFree {I : IsaData} (hI : GuardsSpFree I) (d n nCar : Nat)
    {initOps : List LOperand} {countOp : LOperand} {bodyC : List LinstrRM}
    {bodyOps : List LOperand} (bodyD : Nat) (hi : ∀ o ∈ initOps, opSpB "RSP" o = false)
    (hc : opSpB "RSP" countOp = false) (hb : ∀ i ∈ bodyC, spFreeB "RSP" i.fst = true)
    (ho : ∀ o ∈ bodyOps, opSpB "RSP" o = false) :
    ∀ i ∈ forFrame d n nCar initOps countOp bodyC bodyOps bodyD I,
      spFreeB "RSP" i.fst = true := by
  intro i hmem
  simp only [forFrame, List.mem_append, List.mem_cons, List.mem_map] at hmem
  rcases hmem with h | h | ⟨g, hg, rfl⟩ | rfl | h | h | h | ⟨g, hg, rfl⟩ | rfl | h
  · exact seedMoves_spFree (fun r hr => opSpB_carriedRegs hr) hi i h
  · refine seedMoves_spFree (fun r hr => ?_) (fun o ho' => ?_) i h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact opSpB_regName _
      · exact opSpB_loopCtr _
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho'
      rcases ho' with rfl | rfl
      · rfl
      · exact hc
  · exact hI.zeroTrip _ _ _ (opSpB_loopCtr _) g hg
  · rfl
  · exact hb i h
  · exact parMoves_spFree _ (fun r hr => opSpB_carriedRegs hr) ho i h
  · exact advanceOps_spFree (opSpB_regName _) (opSpB_loopCtr _) i h
  · exact hI.loop _ _ (opSpB_loopCtr _) g hg
  · rfl
  · exact shiftMoves_spFree _ _ i h

/-- The register of an operand in register form does not name `RSP` when the operand does
    not. -/
theorem opSpB_operandName {o : LOperand} (h : o = .reg (operandName o))
    (hs : opSpB "RSP" o = false) : opSpB "RSP" (.reg (operandName o)) = false := by
  rw [h] at hs
  exact hs

/-- Array moves do not name `RSP` when neither their registers nor their names do. -/
theorem arrMoves_spFree {z t : String} {mv : List ArrMove}
    (hz : opSpB "RSP" (.reg z) = false) (ht : opSpB "RSP" (.reg t) = false)
    (hm : ∀ a ∈ mv, opSpB "RSP" (.reg a.dst) = false ∧ opSpB "RSP" (.reg a.src) = false) :
    ∀ i ∈ arrMoves z t mv, spFreeB "RSP" i.fst = true := by
  intro i hi
  simp only [arrMoves, List.mem_flatMap, arrMove, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  obtain ⟨a, ha, rfl | rfl⟩ := hi
  · exact spFreeB_lopn ht fun o ho => by
      rw [List.mem_singleton.mp ho]
      exact opSpB_arrIdx _ (hm a ha).2 hz
  · exact spFreeB_lopn (hm a ha).1 fun o ho => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl
      · exact opSpB_arrIdx _ (hm a ha).2 hz
      · exact ht

/-- Typed moves do not name `RSP` when neither their registers nor the names of their
    pairs do. -/
theorem typedMoves_spFree {z t : String} {tp : List (JasminTy × String × String)}
    (hz : opSpB "RSP" (.reg z) = false) (ht : opSpB "RSP" (.reg t) = false)
    (hp : ∀ p ∈ tp, opSpB "RSP" (.reg p.2.1) = false ∧ opSpB "RSP" (.reg p.2.2) = false) :
    ∀ i ∈ typedMoves z t tp, spFreeB "RSP" i.fst = true := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact arrMoves_spFree hz ht (fun a ha => hp _ (of_mem_arrPairs ha)) i hi
  · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hi
    obtain ⟨ty, hq⟩ := of_mem_regPairs hp'
    exact spFreeB_movI (hp _ hq).1 (hp _ hq).2

/-- A parallel assignment of arrays does not name `RSP` when neither its registers nor
    the names of its moves do. -/
theorem arrParMoves_spFree {z t : String} (D : Nat) {mv : List ArrMove}
    (hz : opSpB "RSP" (.reg z) = false) (ht : opSpB "RSP" (.reg t) = false)
    (hm : ∀ a ∈ mv, opSpB "RSP" (.reg a.dst) = false ∧ opSpB "RSP" (.reg a.src) = false) :
    ∀ i ∈ arrParMoves z t D mv, spFreeB "RSP" i.fst = true := by
  intro i hi
  unfold arrParMoves at hi
  split at hi
  · exact arrMoves_spFree hz ht hm i hi
  · rcases List.mem_append.mp hi with hi | hi
    · exact arrMoves_spFree hz ht (fun q hq => by
        obtain ⟨j, a, ha, rfl⟩ := mem_arrStage hq
        exact ⟨opSpB_regName _, (hm a ha).2⟩) i hi
    · exact arrMoves_spFree hz ht (fun q hq => by
        obtain ⟨j, a, ha, rfl⟩ := mem_arrCommit hq
        exact ⟨(hm a ha).1, opSpB_regName _⟩) i hi

/-- The frame of a counted loop with carried arrays does not name `RSP` when its body and
    the registers of its operands do not. -/
theorem forArrFrame_spFree {I : IsaData} (hI : GuardsSpFree I) (d n : Nat)
    (cs : Ctxt jasminDialect) {initOps : List LOperand} {countOp : LOperand}
    {bodyC : List LinstrRM} {bodyOps : List LOperand} (bodyD : Nat)
    (hi : ∀ o ∈ initOps, opSpB "RSP" (.reg (operandName o)) = false)
    (hc : opSpB "RSP" countOp = false)
    (hb : ∀ i ∈ bodyC, spFreeB "RSP" i.fst = true)
    (ho : ∀ o ∈ bodyOps, opSpB "RSP" (.reg (operandName o)) = false) :
    ∀ i ∈ forArrFrame d n cs initOps countOp bodyC bodyOps bodyD I,
      spFreeB "RSP" i.fst = true := by
  have hpairs : ∀ (ops : List LOperand),
      (∀ o ∈ ops, opSpB "RSP" (.reg (operandName o)) = false) →
      ∀ p ∈ carriedPairs cs (carriedRegs (d + 1) cs.length) ops,
        opSpB "RSP" (.reg p.2.1) = false ∧ opSpB "RSP" (.reg p.2.2) = false :=
    fun ops h p hp => by
      obtain ⟨⟨j, -, h1⟩, o, ho', h2⟩ := carriedPairs_names hp
      rw [h1, h2]
      exact ⟨opSpB_regName _, h o ho'⟩
  intro i hmem
  simp only [forArrFrame, List.mem_append, List.mem_cons, List.mem_map] at hmem
  rcases hmem with rfl | h | h | ⟨g, hg, rfl⟩ | rfl | h | rfl | h | h | h | ⟨g, hg, rfl⟩ | rfl
    | rfl | h
  · exact spFreeB_movI (opSpB_regName _) rfl
  · exact typedMoves_spFree (opSpB_regName _) (opSpB_regName _) (hpairs _ hi) i h
  · refine seedMoves_spFree (fun r hr => ?_) (fun o ho' => ?_) i h
    · rw [List.mem_singleton.mp hr]
      exact opSpB_loopCtr _
    · rw [List.mem_singleton.mp ho']
      exact hc
  · exact hI.zeroTrip _ _ _ (opSpB_loopCtr _) g hg
  · rfl
  · exact hb i h
  · exact spFreeB_movI (opSpB_regName _) rfl
  · exact arrParMoves_spFree _ (opSpB_regName _) (opSpB_regName _)
      (fun a ha => hpairs _ ho _ (of_mem_arrPairs ha)) i h
  · exact parMoves_spFree _
      (fun r hr => by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
        obtain ⟨ty, hq⟩ := of_mem_regPairs hp
        exact (hpairs _ ho _ hq).1)
      (fun o ho' => by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ho'
        obtain ⟨ty, hq⟩ := of_mem_regPairs hp
        exact (hpairs _ ho _ hq).2) i h
  · exact advanceOps_spFree (opSpB_regName _) (opSpB_loopCtr _) i h
  · exact hI.loop _ _ (opSpB_loopCtr _) g hg
  · rfl
  · exact spFreeB_movI (opSpB_regName _) rfl
  · exact typedMoves_spFree (opSpB_regName _) (opSpB_regName _)
      (fun p hp => by
        obtain ⟨v, h1, h2⟩ := shiftPairs_var (t := p.1) (dst := p.2.1) (src := p.2.2) hp
        rw [h1, h2]
        exact ⟨opSpB_regName _, opSpB_regName _⟩) i h

/-- The frame of a loop in exit-flag form does not name `RSP` when its body and operands
    do not. -/
theorem whileFrame_spFree {I : IsaData} (hI : GuardsSpFree I) (d n nCar : Nat)
    {initOps : List LOperand} {bodyC : List LinstrRM} {flagOp : LOperand}
    {bodyOps : List LOperand} (bodyD : Nat) (hi : ∀ o ∈ initOps, opSpB "RSP" o = false)
    (hb : ∀ i ∈ bodyC, spFreeB "RSP" i.fst = true) (hf : opSpB "RSP" flagOp = false)
    (ho : ∀ o ∈ bodyOps, opSpB "RSP" o = false) :
    ∀ i ∈ whileFrame d n nCar initOps bodyC flagOp bodyOps bodyD I,
      spFreeB "RSP" i.fst = true := by
  intro i hmem
  simp only [whileFrame, List.mem_append, List.mem_cons, List.mem_map] at hmem
  rcases hmem with h | rfl | h | h | h | ⟨g, hg, rfl⟩
  · exact seedMoves_spFree (fun r hr => opSpB_carriedRegs hr) hi i h
  · rfl
  · exact hb i h
  · exact flagWord_spFree I (opSpB_regName _) (opSpB_regName _) hf i h
  · exact parMoves_spFree _ (fun r hr => opSpB_carriedRegs hr) ho i h
  · exact hI.loop _ _ (opSpB_regName _) g hg

/-- The frame of a branch does not name `RSP` when its branches and operands do not. -/
theorem ifFrame_spFree {I : IsaData} (hI : GuardsSpFree I) (fn : String) (d n nRes : Nat)
    {condOp : LOperand} {thnC : List LinstrRM} {thnOps : List LOperand} (thnD : Nat)
    {elsC : List LinstrRM} {elsOps : List LOperand} (elsD : Nat)
    (hc : opSpB "RSP" condOp = false) (ht : ∀ i ∈ thnC, spFreeB "RSP" i.fst = true)
    (hto : ∀ o ∈ thnOps, opSpB "RSP" o = false) (he : ∀ i ∈ elsC, spFreeB "RSP" i.fst = true)
    (heo : ∀ o ∈ elsOps, opSpB "RSP" o = false) :
    ∀ i ∈ ifFrame fn d n nRes condOp thnC thnOps thnD elsC elsOps elsD I,
      spFreeB "RSP" i.fst = true := by
  intro i hmem
  simp only [ifFrame, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil,
    or_false] at hmem
  rcases hmem with h | ⟨g, hg, rfl⟩ | rfl | h | h | rfl | ⟨g, hg, rfl⟩ | rfl | h | h | rfl
  · exact flagWord_spFree I (opSpB_regName _) (opSpB_regName _) hc i h
  · exact hI.zeroTrip _ _ _ (opSpB_regName _) g hg
  · rfl
  · exact ht i h
  · exact parMoves_spFree _ (fun r hr => opSpB_carriedRegs hr) hto i h
  · exact spFreeB_movI (opSpB_regName _) rfl
  · exact hI.loop _ _ (opSpB_regName _) g hg
  · rfl
  · exact he i h
  · exact parMoves_spFree _ (fun r hr => opSpB_carriedRegs hr) heo i h
  · rfl

/-- **Neither the code nor the returned operands of the export of a program of
    `RegionExportable` name `RSP`**, over an instruction set whose guards do not. -/
theorem exportR_spFree (nArgs : Nat) (fn : String) {I : IsaData} (hI : GuardsSpFree I)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (hp : RegionExportable p) :
    ∀ (d n : Nat) (r : Exported), exportR nArgs fn p d n I = some r →
      (∀ i ∈ r.code, spFreeB "RSP" i.fst = true) ∧ ∀ o ∈ r.res, opSpB "RSP" o = false := by
  induction p with
  | ret vs =>
      intro d n r h
      simp only [exportR, Option.some.injEq] at h
      subst h
      exact ⟨fun i hi => (by cases hi), opSpB_exprArgsHV d nArgs vs⟩
  | var e k ih =>
      intro d n r h
      simp only [exportR, Option.map_eq_some_iff] at h
      obtain ⟨rk, hk, rfl⟩ := h
      obtain ⟨hc, hres⟩ := ih hp.2 _ _ _ hk
      refine ⟨fun i hi => ?_, hres⟩
      rcases List.mem_append.mp hi with hi | hi
      · exact bindOps_spFree nArgs hp.1 d i hi
      · exact hc i hi
  | forLoop count inits body k ihb ihk =>
      intro d n r h
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      obtain ⟨hbc, hbr⟩ := ihb hp.1 _ _ _ hb
      obtain ⟨hc, hres⟩ := ihk hp.2 _ _ _ hk
      refine ⟨fun i hi => ?_, hres⟩
      rcases List.mem_append.mp hi with hi | hi
      · exact forArrFrame_spFree hI _ _ _ _
          (fun o ho => opSpB_operandName (exprArgsHV_isReg _ _ inits o ho)
            (opSpB_exprArgsHV _ _ inits o ho))
          (opSpB_resolveVar count) hbc
          (fun o ho => opSpB_operandName (exportR_res_isReg nArgs fn body _ _ _ hb o ho)
            (hbr o ho)) i hi
      · exact hc i hi
  | ifThenElse cond thn els k iht ihe ihk =>
      intro d n r h
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨t, ht, e, he, rk, hk, rfl⟩ := h
      obtain ⟨htc, htr⟩ := iht hp.2.1 _ _ _ ht
      obtain ⟨hec, her⟩ := ihe hp.2.2.1 _ _ _ he
      obtain ⟨hc, hres⟩ := ihk hp.2.2.2 _ _ _ hk
      refine ⟨fun i hi => ?_, hres⟩
      rcases List.mem_append.mp hi with hi | hi
      · exact ifFrame_spFree hI _ _ _ _ _ _ (opSpB_resolveVar cond) htc htr hec her i hi
      · exact hc i hi
  | whileLoop inits body k ihb ihk =>
      intro d n r h
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      obtain ⟨hbc, hbr⟩ := ihb hp.2.1 _ _ _ hb
      obtain ⟨hc, hres⟩ := ihk hp.2.2 _ _ _ hk
      refine ⟨fun i hi => ?_, hres⟩
      rcases List.mem_append.mp hi with hi | hi
      · refine whileFrame_spFree hI _ _ _ _ (opSpB_exprArgsHV _ _ inits) hbc ?_
          (fun o ho => hbr o (List.mem_of_mem_tail ho)) i hi
        cases hbres : b.res with
        | nil => rfl
        | cons x xs => exact hbr x (by simp [hbres])
      · exact hc i hi
  | call f args k ih =>
      intro d n r h
      obtain ⟨-, rk, hk, rfl⟩ := exportR_call_eq_some.mp h
      obtain ⟨hc, hres⟩ := ih hp.2 _ _ _ hk
      refine ⟨fun i hi => ?_, hres⟩
      rcases List.mem_append.mp hi with hi | hi
      · rw [List.mem_singleton.mp hi]
        exact spFreeB_lopn (opSpB_regName _) (opSpB_exprArgsHV d nArgs args)
      · exact hc i hi

/-- **The export of a program of `RegionExportable` over x86 passes `spFreeBodyB` at
    `RSP`.** -/
theorem exportR_spFreeBodyB (nArgs : Nat) (fn : String) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} {p : NFProg jasminDialect Γ ts} (hp : RegionExportable p)
    {d n : Nat} {r : Exported} (hr : exportR nArgs fn p d n = some r) :
    spFreeBodyB "RSP" r.code = true :=
  List.all_eq_true.mpr (exportR_spFree nArgs fn x86Data_guardsSpFree hp d n r hr).1

/-! ## 6. The return -/

/-- **The run of the exported code followed by a return.** Let `p` be a program of
    `RegionExportable` with the export `r`, and let `p` denote `v` at `V`. From an entry
    state at the counter `0` whose store agrees with `V`, with the stack pointer `RSP`
    holding `sp - 8` and the memory cell it addresses holding the word of a counter `ra`
    below `2 ^ 64`, the instruction set with calls makes on the code followed by `Lret` a
    run to the counter `ra` with `RSP` holding `sp`. The end state is that of the run
    without the stack pointer, `t`, with the stack pointer and its cell replaced; `t`
    agrees with the returned operands at `v`. -/
theorem exportR_ret_steps (fn : String) (tag : MemTag) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} {p : NFProg jasminDialect Γ ts} (hp : RegionExportable p)
    {r : Exported} (hr : exportR Γ.length fn p Γ.length 0 = some r) (fuel : Nat)
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
  obtain ⟨k, t, hrun, hat, hres, hfr, -⟩ := exportRSim_lsemFuelMemF
    (exportR_sim Γ.length fn hp) hr rfl le_rfl fuel V v hden b0 zf hpc hag
  have hrun0 := hrun 0
  rw [← X86Backend.X86Isa.x86Isa_lsemFuelMemF] at hrun0
  have hrun' : x86Isa.lsemFuelMemF (singletonProgM fn r.code) (k + 0)
      (spFrame "RSP" (sp - 8) (BitVec.ofNat 64 ra)
        { prog := { base := b0, lfn := fn }, zf := zf })
      = some (spFrame "RSP" (sp - 8) (BitVec.ofNat 64 ra) t) := by
    rw [x86_lsemFuelMemF_spFrame (P := singletonProgM fn r.code)
      (spFree_of_spFreeBodyB (exportR_spFreeBodyB _ fn hp hr)), hrun0]
    rfl
  obtain ⟨n, -, hsteps, hatr⟩ := x86_steps_snoc_ret (tag := tag)
    (exportR_noCall _ _ x86Data_guardsNoCall p _ _ _ hr) hrun' ⟨hat.1, hat.2⟩
    (LstateN.getW_setReg_same _ _ _)
    (show (spM "RSP" (sp - 8) (BitVec.ofNat 64 ra) t.prog.base).lmem "RSP" (sp - 8).toInt
        = BitVec.ofNat 64 ra by simp [spM, LstateM.storeMemC]) hra
  exact ⟨n, t, hsteps, hatr, hres, hfr⟩

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
