/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeCopn
public import CatCrypt.Crypto.SecureCompilation.VIR.CallLowering

/-!
# The `Com ↔ Jasmin` bridge for the leaf `Ccall` arm

`JasminPrint.lowerExpr` lowers a leaf call (`extCall`, and the ops lowered the
same way) to

```
Ccall DoInline [Lvar dst] {name} (args.map Pvar)
```

over register arguments, and the JasminPrint evaluator stores the leaf result at
`dst`. This file relates that instruction's run under the `psem.v` mirror
(`execInstrR`, `Ccall` arm, `CallLowering.execInstrR_Ccall_eq`) to the JasminPrint
store update, in the shape of `ComJasminBridgeCopn.copn_ror_simulates`.

## The callee

The mirror runs the callee `fn` from the program `prog` (`execCall`). The bridge
is stated under the hypothesis that this run, on the argument words read from
the registers, returns one register word `r` (with any syscall state and
memory). The argument reads are derived from `StateCorrReg`: the JasminPrint
store holds the same words the mirror passes to the callee. `idProg` is a
program whose function `id` returns its argument, and `execCall_idProg` shows
the callee hypothesis holds for it.

## Contents

* `CallArg`, `CallArg.expr`, `CallArg.value`, `callInstr` — the mirror image of
  the emitted call.
* `semPexprs_callArgs` / `store_get_callArgs` — the mirror argument evaluation and
  the agreeing JasminPrint reads.
* `ccall_leaf_simulates` / `ccall_leaf_endToEnd` — the call run, the argument
  agreement, the post-state correspondence to `Store.set st dst.vname r`, and the
  relational `SemIr` step.
* `idProg`, `execCall_idProg`, `ccall_id_endToEnd` — the bridge instantiated at
  the identity callee.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeCall

open CatCrypt.Crypto.Jasmin.CoqSemMirror
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.StateBijection
open CatCrypt.Crypto.SecureCompilation.VIR.ExecAdequacy
open CatCrypt.Crypto.SecureCompilation.VIR.OperandReadCorr

variable {SyscallState Mem : Type} [MemModel Mem]

/-! ## §1. The emitted call -/

/-- One register argument of a call: the source register `src` and the word
    `w` of width `sz` it holds. -/
structure CallArg where
  /-- Source register. -/
  src : VarI
  /-- Register width. -/
  sz : WSize
  /-- The word the register holds. -/
  w : BitVec sz.bits

/-- The argument expression `Pvar src`. -/
def CallArg.expr (a : CallArg) : Pexpr := .Pvar (mkLvar a.src)

/-- The argument value `Vword sz w`. -/
def CallArg.value (a : CallArg) : Value := .Vword a.sz a.w

/-- The emitted leaf call `Ccall [Lvar dst] fn (args.map Pvar)`. -/
def callInstr (dst : VarI) (fn : FunName) (args : List CallArg) : InstrR :=
  .Ccall [.Lvar dst] fn (args.map CallArg.expr)

/-- Every argument register lies in the frame `names` and holds its word in `s`. -/
def CallArgsRead (names : List Var) (s : Estate SyscallState Mem)
    (args : List CallArg) : Prop :=
  ∀ a ∈ args, a.src.v_var ∈ names ∧ (s.evm).get a.src.v_var = .Vword a.sz a.w

/-- The mirror evaluates the argument registers to their words. -/
theorem semPexprs_callArgs (gd : GlobDecls) (opS : OpSem)
    (s : Estate SyscallState Mem) :
    ∀ (args : List CallArg), (∀ a ∈ args, (s.evm).get a.src.v_var = .Vword a.sz a.w) →
      semPexprs (Mem := Mem) true gd opS s (args.map CallArg.expr)
        = .ok (args.map CallArg.value)
  | [], _ => rfl
  | a :: rest, h => by
    have ha := semPexpr_pvar_vword (Mem := Mem) gd opS s a.src a.sz a.w
      (h a List.mem_cons_self)
    have hrest := semPexprs_callArgs gd opS s rest
      (fun b hb => h b (List.mem_cons_of_mem a hb))
    show (do
        let v ← semPexpr (Mem := Mem) true gd opS s a.expr
        let vs ← semPexprList (Mem := Mem) true gd opS s (rest.map CallArg.expr)
        .ok (v :: vs)) = _
    rw [show a.expr = .Pvar (mkLvar a.src) from rfl, ha]
    show (do
        let vs ← semPexprs (Mem := Mem) true gd opS s (rest.map CallArg.expr)
        (.ok (a.value :: vs) : JResult Values)) = _
    rw [hrest]
    rfl

/-- Under `StateCorrReg`, the JasminPrint store reads each argument register to
    the same word the mirror passes to the callee. -/
theorem store_get_callArgs (gd : GlobDecls) (opS : OpSem)
    (s : Estate SyscallState Mem) (st : Store) (names : List Var)
    (args : List CallArg) (hcorr : StateCorrReg names st (s.evm))
    (hargs : CallArgsRead names s args) :
    ∀ a ∈ args, Store.get st a.src.v_var.vname (.reg a.sz.bits) = a.w := by
  intro a ha
  obtain ⟨hm, hr⟩ := hargs a ha
  exact (pvar_read_corr (Mem := Mem) gd opS s st names a.src a.sz a.w hcorr hm hr).2

/-! ## §2. The paired step -/

/-- **Simulation (paired step) for the emitted leaf call.** Let `dst` be a
    register of width `sz`, frame-distinct from `names`, and let every argument
    register lie in `names` and hold its word. If the JasminPrint `Store` `st`
    corresponds to the mirror `Vm` on `names`, and the mirror callee run on the
    argument words returns `[Vword sz r]` with syscall state `scs'` and memory
    `m'`, then:

    * the mirror `Ccall` run (fuel `fuel+1`) lands the state with `escs := scs'`,
      `emem := m'` and `Vm` `s.evm.set dst (Vword sz r)`;
    * the JasminPrint store reads every argument register to the word passed to
      the callee; and
    * the post-state corresponds (`StateCorrReg (dst :: names)`) to
      `Store.set st dst.vname r`. -/
theorem ccall_leaf_simulates
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog) (fuel : Nat)
    (dst : VarI) (fn : FunName) (args : List CallArg) (sz : WSize) (r : BitVec sz.bits)
    (s : Estate SyscallState Mem) (st : Store) (names : List Var)
    (scs' : SyscallState) (m' : Mem)
    (hdst : dst.v_var.vtype = .aword sz)
    (hargs : CallArgsRead names s args)
    (hdistinct : ∀ r' ∈ names, r' ≠ dst.v_var ∧ r'.vname ≠ dst.v_var.vname)
    (hcorr : StateCorrReg names st (s.evm))
    (hcall : execCall (Mem := Mem) aS opS gd fuel s.escs s.emem fn
        (args.map CallArg.value) prog = .ok (scs', m', [.Vword sz r])) :
    execInstrR (Mem := Mem) aS opS gd (fuel + 1) s (callInstr dst fn args) prog
      = .ok ({ s with escs := scs', emem := m', evm := (s.evm).set dst.v_var (.Vword sz r) })
    ∧ (∀ a ∈ args, Store.get st a.src.v_var.vname (.reg a.sz.bits) = a.w)
    ∧ StateCorrReg (dst.v_var :: names)
        (Store.set st dst.v_var.vname (t := .reg sz.bits) r)
        ((s.evm).set dst.v_var (.Vword sz r)) := by
  refine ⟨?_, store_get_callArgs gd opS s st names args hcorr hargs,
    stateCorrReg_write dst.v_var sz r st s.evm names hdst hdistinct hcorr⟩
  rw [callInstr, CallLowering.execInstrR_Ccall_eq]
  unfold CallLowering.callComposition
  rw [semPexprs_callArgs gd opS s args (fun a ha => (hargs a ha).2)]
  show (do
      let triple ← execCall (Mem := Mem) aS opS gd fuel s.escs s.emem fn
        (args.map CallArg.value) prog
      writeLvals (Mem := Mem) true gd opS
        ({ s with escs := triple.1, emem := triple.2.1 }) [.Lvar dst] triple.2.2) = _
  rw [hcall]
  show (do
      let s1 ← writeVar (Mem := Mem) true dst (.Vword sz r) { s with escs := scs', emem := m' }
      JResult.fold2 (.otherErr "write_lvals length mismatch")
        (fun x v st => writeLval (Mem := Mem) true gd opS x v st) [] [] s1) = _
  unfold writeVar setVar
  rw [hdst]
  simp only [DB, Value.isDefined, truncatable, Value.typeOf,
    Bool.not_true, decide_true, Bool.true_and]
  rfl

/-- **End-to-end bridge for the emitted leaf call.** Under the hypotheses of
    `ccall_leaf_simulates`, the emitted `Ccall` witnesses the relational step
    `SemIr` to the post-state, and that state's `Vm` corresponds to
    `Store.set st dst.vname r`. -/
theorem ccall_leaf_endToEnd
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog) (fuel : Nat)
    (dst : VarI) (fn : FunName) (args : List CallArg) (sz : WSize) (r : BitVec sz.bits)
    (s : Estate SyscallState Mem) (st : Store) (names : List Var)
    (scs' : SyscallState) (m' : Mem)
    (hdst : dst.v_var.vtype = .aword sz)
    (hargs : CallArgsRead names s args)
    (hdistinct : ∀ r' ∈ names, r' ≠ dst.v_var ∧ r'.vname ≠ dst.v_var.vname)
    (hcorr : StateCorrReg names st (s.evm))
    (hcall : execCall (Mem := Mem) aS opS gd fuel s.escs s.emem fn
        (args.map CallArg.value) prog = .ok (scs', m', [.Vword sz r])) :
    SemIr (Mem := Mem) aS opS gd prog s (callInstr dst fn args)
        { s with escs := scs', emem := m', evm := (s.evm).set dst.v_var (.Vword sz r) }
    ∧ StateCorrReg (dst.v_var :: names)
        (Store.set st dst.v_var.vname (t := .reg sz.bits) r)
        ((s.evm).set dst.v_var (.Vword sz r)) := by
  obtain ⟨hrun, _, hcorr'⟩ :=
    ccall_leaf_simulates aS opS gd prog fuel dst fn args sz r s st names scs' m'
      hdst hargs hdistinct hcorr hcall
  exact ⟨execInstrR_sound (n := fuel + 1) aS opS gd prog hrun, hcorr'⟩

/-! ## §3. The identity callee -/

/-- The parameter/return register `x : aword sz` of the identity function. -/
def idVar (sz : WSize) : VarI := { v_var := { vname := "x", vtype := .aword sz } }

/-- The program with one function `id` of width `sz`: parameter `x`, empty body,
    returning `x`. -/
def idProg (sz : WSize) : Prog :=
  { pFuncs := [({ name := "id" },
      { tyin := [.aword sz], params := [idVar sz], body := [],
        tyout := [.aword sz], rets := [idVar sz] })],
    pGlobs := [] }

/-- The mirror run of `id` on a word returns that word, with syscall state and
    memory unchanged. -/
theorem execCall_idProg (aS : AsmSem) (opS : OpSem) (gd : GlobDecls)
    (fuel : Nat) (scs : SyscallState) (m : Mem) (sz : WSize) (w : BitVec sz.bits) :
    execCall (Mem := Mem) aS opS gd (fuel + 1) scs m { name := "id" } [.Vword sz w] (idProg sz)
      = .ok (scs, m, [.Vword sz w]) := by
  simp [execCall, getFunDef, idProg, JResult.mapM, ComJasminBridgeFull.truncateVal_aword_self,
    evalAtype, writeVars, JResult.fold2, writeVar, setVar, idVar, DB, truncatable,
    Value.isDefined, Value.typeOf, CmdRun.execCmd_nil, getVarIs, getVar, Vm.get, Vm.set,
    Estate.withVm, JResult.bind]

/-- **The leaf-call bridge at the identity callee.** For `dst := id(src)` over
    `idProg sz`, with `src` in the frame holding `Vword sz w`, the emitted `Ccall`
    witnesses `SemIr` to `s.evm.set dst (Vword sz w)`, and that state corresponds
    to `Store.set st dst.vname w`. The callee hypothesis of `ccall_leaf_endToEnd`
    is discharged by `execCall_idProg`. -/
theorem ccall_id_endToEnd
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (fuel : Nat)
    (dst src : VarI) (sz : WSize) (w : BitVec sz.bits)
    (s : Estate SyscallState Mem) (st : Store) (names : List Var)
    (hdst : dst.v_var.vtype = .aword sz)
    (hmem : src.v_var ∈ names)
    (hread : (s.evm).get src.v_var = .Vword sz w)
    (hdistinct : ∀ r' ∈ names, r' ≠ dst.v_var ∧ r'.vname ≠ dst.v_var.vname)
    (hcorr : StateCorrReg names st (s.evm)) :
    SemIr (Mem := Mem) aS opS gd (idProg sz) s
        (callInstr dst { name := "id" } [⟨src, sz, w⟩])
        { s with escs := s.escs, emem := s.emem, evm := (s.evm).set dst.v_var (.Vword sz w) }
    ∧ StateCorrReg (dst.v_var :: names)
        (Store.set st dst.v_var.vname (t := .reg sz.bits) w)
        ((s.evm).set dst.v_var (.Vword sz w)) :=
  ccall_leaf_endToEnd aS opS gd (idProg sz) (fuel + 1) dst { name := "id" } [⟨src, sz, w⟩]
    sz w s st names s.escs s.emem hdst
    (fun a ha => by
      rcases List.mem_singleton.mp ha with rfl
      exact ⟨hmem, hread⟩)
    hdistinct hcorr (execCall_idProg aS opS gd fuel s.escs s.emem sz w)

end CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeCall
