/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeExt

/-!
# `Com ↔ Jasmin` bridge extension, part 2: the `signext` and narrowing width-casts

`ComJasminBridgeExt` closes the widening `castW` shape
`Papp1 (Ozeroext szo szi) (Pvar a)` (zero-extend). This file adds two more
`Papp1` width-cast shapes, each a mechanical mirror of that skeleton:

* **`Osignext` (signed width-cast).** The mirror unop `SOp1.Osignext szo szi`
  sign-extends the source word: on a `Vword szi w` it returns
  `Vword szo (BitVec.signExtend szo.bits w)`, the sign-extension the reference
  `JasminTranslate.evalSop1 (Osignext …)` computes
  (`signExtendWord wsi wso v = v.signExtend wso.bits`). Same read-correspondence
  (source register read via `pvar_read_corr`), same per-step + end-to-end bridge
  (through `cassgn_regArith_simulates` / `cassgn_regArith_endToEnd`, generic in
  the RHS), a worked `x := (s64) y` example.

* **Narrowing `Ozeroext` (`szo < szi`, i.e. `TRUNC`).** The landed
  `ComJasminBridgeExt.zextOpSem` already produces `BitVec.setWidth szo.bits w`,
  which *truncates* when `szo.bits < szi.bits`. So the widening lemmas apply
  unchanged at narrowing widths — no distinct unop is needed. This is exhibited
  as a worked `x := (u8) y` example (`u64 → u8`) reusing
  `ComJasminBridgeExt.cassgn_castW_selfContained`.

## Value coincidence

* `sext_denote_eq_signExtend` — the mirror sign-extend output
  `BitVec.signExtend szo.bits w` is the same `BitVec` as the method-call spelling
  `w.signExtend szo.bits` used by the reference `evalSop1 (Osignext …)` /
  `signExtendWord`. The signed analogue of
  `ComJasminBridgeExt.castW_denote_eq_setWidth`.

## Scope

The jasmin `Com` dialect (`JasminOp`) has no signed width-cast op — its `castW`
denotes `BitVec.zeroExtend` only. The `signext` bridge here is therefore stated
at the mirror + JasminPrint `Store` level, with value coincidence against the
reference `evalSop1 (Osignext …)` sign-extension (`BitVec.signExtend`). The
`Pget`/`stackLoad` array read is *not* closed here: it reads a `.Varr n a` source
slot, and `StateBijection.encodeRegVal` collapses every non-`Vword` value to the
default `reg 0` `DynVal`, so `StateCorrReg`/`RegCorr` carries no array-cell
correspondence — closing `Pget` needs a new array/memref-cell bijection, not a
mechanical port. This matches the honest-scope note in `StateBijection`
(arrays/memory are out of the reg fragment).

0 sorries.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeExt2

open CatCrypt.Crypto.Jasmin.CoqSemMirror
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.StateBijection
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeFull
open CatCrypt.Crypto.SecureCompilation.VIR.OperandReadCorr
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeExt

variable {SyscallState Mem : Type} [MemModel Mem]

/-! ## §1. The signed width-cast unop `OpSem`

`signext`'s mirror unop is `SOp1.Osignext szo szi` — sign-extend the input word
(width `szi`) to the output width `szo`. Its `OpSem` (`sextOpSem`) maps a
matching-width `Vword szi w` to `Vword szo (BitVec.signExtend szo.bits w)`. Other
shapes are type errors (out of the reg fragment). -/

/-- The signed width-cast (`signext`) `OpSem`: `Osignext szo szi` on a
    `Vword szi w` returns the sign-extended `Vword szo (BitVec.signExtend szo.bits
    w)`. Both widths are checked against the operator's tags (defensive `if`, as
    in `ComJasminBridgeExt.zextOpSem`). -/
def sextOpSem (szo szi : WSize) : OpSem where
  sem_sop1 := fun
    | .Osignext szo' _szi', .Vword sz'' w =>
        if h : szo' = szo ∧ sz'' = szi then
          .ok (.Vword szo (BitVec.signExtend szo.bits (h.2 ▸ w)))
        else .typeError
    | _, _ => .typeError
  sem_sop2 := fun _ _ _ => .typeError
  sem_opN := fun _ _ => .typeError

/-- **The signed width-cast unop evaluates to the sign-extension.**
    `sextOpSem szo szi` applied to `Osignext szo szi` and a matching-width
    `Vword szi w` returns `.ok (.Vword szo (BitVec.signExtend szo.bits w))`. -/
theorem sextOpSem_sem (szo szi : WSize) (w : BitVec szi.bits) :
    (sextOpSem szo szi).sem_sop1 (.Osignext szo szi) (.Vword szi w)
      = .ok (.Vword szo (BitVec.signExtend szo.bits w)) := by
  show (if h : szo = szo ∧ szi = szi then
          (.ok (.Vword szo (BitVec.signExtend szo.bits (h.2 ▸ w))) : JResult Value)
        else .typeError) = _
  rw [dif_pos ⟨rfl, rfl⟩]

/-- **Value coincidence (signed).** The mirror sign-extend output
    `BitVec.signExtend szo.bits w` is the *same* `BitVec` as the method-call
    spelling `w.signExtend szo.bits` that the reference `evalSop1 (Osignext …)`
    computes (`signExtendWord wsi wso v = v.signExtend wso.bits`). The signed
    analogue of `ComJasminBridgeExt.castW_denote_eq_setWidth`. -/
theorem sext_denote_eq_signExtend (szo szi : WSize) (w : BitVec szi.bits) :
    (w.signExtend szo.bits) = BitVec.signExtend szo.bits w := rfl

/-! ## §2. The `signext` operand-read correspondence

The mirror `semPexpr` of `Papp1 (Osignext szo szi) (Pvar a)` evaluates the
operand `Pvar a` (via `OperandReadCorr.semPexpr_pvar_vword`) to the source word,
then applies the sign-extend unop. Under `StateCorrReg`, the source word is
exactly what the JasminPrint `Store` holds at `a` (`pvar_read_corr`). -/

/-- The mirror `semPexpr` of `Papp1 (Osignext szo szi) (Pvar a)`, when `a` reads
    `Vword szi w`, is `.ok (.Vword szo (BitVec.signExtend szo.bits w))`. Composes
    `OperandReadCorr.semPexpr_pvar_vword` (operand read) with `sextOpSem_sem`. -/
theorem semPexpr_papp1_signext
    (gd : GlobDecls) (s : Estate SyscallState Mem)
    (a : VarI) (szo szi : WSize) (w : BitVec szi.bits)
    (hread : (s.evm).get a.v_var = .Vword szi w) :
    semPexpr (Mem := Mem) true gd (sextOpSem szo szi) s
        (.Papp1 (.Osignext szo szi) (.Pvar (mkLvar a)))
      = .ok (.Vword szo (BitVec.signExtend szo.bits w)) := by
  show (do
      let v1 ← semPexpr (Mem := Mem) true gd (sextOpSem szo szi) s (.Pvar (mkLvar a))
      (sextOpSem szo szi).sem_sop1 (.Osignext szo szi) v1) = _
  rw [semPexpr_pvar_vword gd (sextOpSem szo szi) s a szi w hread]
  exact sextOpSem_sem szo szi w

/-- **`signext`-read correspondence.** Under `StateCorrReg names st vm`, for a
    source register `a ∈ names` reading `Vword szi w`:

    * the mirror `semPexpr` of `Papp1 (Osignext szo szi) (Pvar a)` is
      `.ok (.Vword szo (BitVec.signExtend szo.bits w))` — the sign-extended
      source; and
    * the JasminPrint `Store.get st a.vname (.reg szi.bits)` is the *same* source
      word `w`.

    The RHS value is *computed from the corresponding register*, not supplied.
    The signed analogue of `ComJasminBridgeExt.papp1_zeroext_read_corr`. -/
theorem papp1_signext_read_corr
    (gd : GlobDecls) (s : Estate SyscallState Mem) (st : Store)
    (names : List Var) (a : VarI) (szo szi : WSize) (w : BitVec szi.bits)
    (hcorr : StateCorrReg names st (s.evm))
    (hmem : a.v_var ∈ names)
    (hread : (s.evm).get a.v_var = .Vword szi w) :
    semPexpr (Mem := Mem) true gd (sextOpSem szo szi) s
        (.Papp1 (.Osignext szo szi) (.Pvar (mkLvar a)))
      = .ok (.Vword szo (BitVec.signExtend szo.bits w))
    ∧ Store.get st a.v_var.vname (.reg szi.bits) = w := by
  refine ⟨semPexpr_papp1_signext gd s a szo szi w hread, ?_⟩
  exact (pvar_read_corr gd (sextOpSem szo szi) s st names a szi w hcorr hmem hread).2

/-! ## §3. The self-contained per-step `signext` bridge

`ComJasminBridgeFull.cassgn_regArith_simulates` is generic in the RHS expression
`e` and its value `w`. We *derive* `hrhs` for the `signext` shape from
`papp1_signext_read_corr` and feed it through: the destination width is the
*output* width `szo`, the produced value is the sign-extended source. -/

/-- **Self-contained per-step `signext` bridge (RHS derived).** For
    `dst := (Osignext szo szi) a` (destination register of width `szo`), given a
    source register `a ∈ names` holding `Vword szi w` and corresponding states,
    the mirror `Cassgn` run lands
    `s.withVm (s.evm.set dst (.Vword szo (BitVec.signExtend szo.bits w)))`, and the
    post-state corresponds (`StateCorrReg (dst :: names)`) to the JasminPrint
    `Store.set st dst (BitVec.signExtend szo.bits w)`. The RHS value is derived
    from the operand read, not assumed. Threads through
    `cassgn_regArith_simulates`. -/
theorem cassgn_signext_selfContained
    (gd : GlobDecls) (tag : AssgnTag)
    (dst a : VarI) (szo szi : WSize)
    (s : Estate SyscallState Mem) (st : Store) (names : List Var)
    (w : BitVec szi.bits)
    (hdst : dst.v_var.vtype = .aword szo)
    (hmem : a.v_var ∈ names)
    (hread : (s.evm).get a.v_var = .Vword szi w)
    (hdistinct : ∀ r' ∈ names, r' ≠ dst.v_var ∧ r'.vname ≠ dst.v_var.vname)
    (hcorr : StateCorrReg names st (s.evm)) :
    OpSemCoverage.assignExec (Mem := Mem) (sextOpSem szo szi) gd (.Lvar dst)
        (.aword szo)
        (.Papp1 (.Osignext szo szi) (.Pvar (mkLvar a))) s
      = .ok (s.withVm ((s.evm).set dst.v_var
          (.Vword szo (BitVec.signExtend szo.bits w))))
    ∧ StateCorrReg (dst.v_var :: names)
        (Store.set st dst.v_var.vname (t := .reg szo.bits)
          (BitVec.signExtend szo.bits w))
        ((s.evm).set dst.v_var (.Vword szo (BitVec.signExtend szo.bits w))) := by
  obtain ⟨hrhs, _⟩ :=
    papp1_signext_read_corr gd s st names a szo szi w hcorr hmem hread
  exact cassgn_regArith_simulates (SyscallState := SyscallState) (Mem := Mem)
    gd (sextOpSem szo szi) dst szo tag
    (.Papp1 (.Osignext szo szi) (.Pvar (mkLvar a)))
    (BitVec.signExtend szo.bits w) s st names hdst hrhs hdistinct hcorr

/-! ## §4. The end-to-end `signext` bridge (adequacy)

Chaining `ComJasminBridgeFull.cassgn_regArith_endToEnd`: the mirror run of the
translated `signext` `Cassgn` *witnesses* the reference `psem.v` relational step
`SemIr`, and the post-state corresponds. -/

/-- **End-to-end per-step `signext` bridge.** For the `signext` `Cassgn`
    `dst := (Osignext szo szi) a`, at fuel `fuel+1`, the mirror run witnesses the
    reference relational step `SemIr` landing
    `s.withVm (s.evm.set dst (.Vword szo (signExtend …)))`, and the post-state
    corresponds (`StateCorrReg`) to the JasminPrint
    `Store.set st dst (BitVec.signExtend szo.bits w)`. RHS derived via
    `papp1_signext_read_corr`. -/
theorem cassgn_signext_endToEnd
    (aS : AsmSem) (gd : GlobDecls) (prog : Prog)
    (dst a : VarI) (szo szi : WSize) (tag : AssgnTag)
    (s : Estate SyscallState Mem) (st : Store) (names : List Var) (fuel : Nat)
    (w : BitVec szi.bits)
    (hdst : dst.v_var.vtype = .aword szo)
    (hmem : a.v_var ∈ names)
    (hread : (s.evm).get a.v_var = .Vword szi w)
    (hdistinct : ∀ r' ∈ names, r' ≠ dst.v_var ∧ r'.vname ≠ dst.v_var.vname)
    (hcorr : StateCorrReg names st (s.evm)) :
    SemIr (Mem := Mem) aS (sextOpSem szo szi) gd prog s
        (.Cassgn (.Lvar dst) tag (.aword szo)
          (.Papp1 (.Osignext szo szi) (.Pvar (mkLvar a))))
        (s.withVm ((s.evm).set dst.v_var
          (.Vword szo (BitVec.signExtend szo.bits w))))
    ∧ StateCorrReg (dst.v_var :: names)
        (Store.set st dst.v_var.vname (t := .reg szo.bits)
          (BitVec.signExtend szo.bits w))
        ((s.evm).set dst.v_var (.Vword szo (BitVec.signExtend szo.bits w))) := by
  obtain ⟨hrhs, _⟩ :=
    papp1_signext_read_corr gd s st names a szo szi w hcorr hmem hread
  exact cassgn_regArith_endToEnd (SyscallState := SyscallState) (Mem := Mem)
    aS (sextOpSem szo szi) gd prog dst szo tag
    (.Papp1 (.Osignext szo szi) (.Pvar (mkLvar a)))
    (BitVec.signExtend szo.bits w) s st names fuel hdst hrhs hdistinct hcorr

/-! ## §5. Worked example: `x := (s64) y` (`reg u32 → reg u64` sign-widen)

The signed width-cast `x := (s64) y` (`y : reg u32`, `x : reg u64`), with the RHS
value *computed from the `Store`* (`y` read from a corresponding register). From
`y = 0xFFFFFFFF : BitVec 32` (i.e. `-1`) the sign-extended result is
`0xFFFFFFFFFFFFFFFF : BitVec 64`. -/

namespace SignExtExample

/-- `x : reg u64` (the sign-widened destination). -/
def xVar : VarI := { v_var := { vname := "x", vtype := .aword .U64 } }
/-- `y : reg u32` (the narrow source, holding `-1`). -/
def yVar : VarI := { v_var := { vname := "y", vtype := .aword .U32 } }

/-- A start `Estate` holding `y = Vword U32 0xFFFFFFFF` (the two's-complement
    `-1`). -/
def startState : Estate Unit OpSemCoverage.AssignExample.TrivialMem :=
  { escs := (), emem := (),
    evm := Vm.set Vm.init yVar.v_var (.Vword .U32 (0xFFFFFFFF : BitVec 32)) }

theorem startState_y :
    (startState.evm).get yVar.v_var = .Vword .U32 (0xFFFFFFFF : BitVec 32) := by
  show (Vm.set Vm.init yVar.v_var (.Vword .U32 (0xFFFFFFFF : BitVec 32))).get
        yVar.v_var = _
  simp [Vm.get, Vm.set]

/-- **The sign-widened RHS `(s64) y` is DERIVED (not supplied).** Given an initial
    `StateCorrReg [y]`, the `signext` RHS `Papp1 (Osignext U64 U32) (Pvar y)`
    *evaluates to* `.ok (.Vword U64 0xFFFFFFFFFFFFFFFF)` — `y`'s `-1` sign-extended
    to `BitVec 64`, computed from the `Store` register `y`. -/
theorem rhs_derived (st : Store)
    (hcorr : StateCorrReg [yVar.v_var] st (startState.evm)) :
    semPexpr (Mem := OpSemCoverage.AssignExample.TrivialMem) true []
        (sextOpSem .U64 .U32) startState
        (.Papp1 (.Osignext .U64 .U32) (.Pvar (mkLvar yVar)))
      = .ok (.Vword .U64 (0xFFFFFFFFFFFFFFFF : BitVec 64))
    ∧ Store.get st yVar.v_var.vname (.reg 32) = (0xFFFFFFFF : BitVec 32) := by
  obtain ⟨heval, hsy⟩ :=
    papp1_signext_read_corr (SyscallState := Unit)
      (Mem := OpSemCoverage.AssignExample.TrivialMem)
      [] startState st [yVar.v_var] yVar .U64 .U32 (0xFFFFFFFF : BitVec 32)
      hcorr (by simp) startState_y
  refine ⟨?_, hsy⟩
  have h : BitVec.signExtend WSize.U64.bits (0xFFFFFFFF : BitVec 32)
      = (0xFFFFFFFFFFFFFFFF : BitVec 64) := by rfl
  rw [← h]
  exact heval

/-- **Worked self-contained `x := (s64) y` step.** From `StateCorrReg [y]` with
    `y = -1 : BitVec 32`, the `signext` `Cassgn` `x := (s64) y` mirror-runs to
    `x = Vword U64 0xFFFFFFFFFFFFFFFF` — the sign-widened value **derived** from
    the `Store` register `y` (`papp1_signext_read_corr`), not supplied; and the
    post-state corresponds (`StateCorrReg [x, y]`) to the JasminPrint
    `Store.set st "x" (0xFFFFFFFFFFFFFFFF : BitVec 64)`. -/
theorem selfContained_signExtExample (st : Store)
    (hcorr : StateCorrReg [yVar.v_var] st (startState.evm)) :
    OpSemCoverage.assignExec
        (Mem := OpSemCoverage.AssignExample.TrivialMem) (sextOpSem .U64 .U32) []
        (.Lvar xVar) (.aword .U64)
        (.Papp1 (.Osignext .U64 .U32) (.Pvar (mkLvar yVar))) startState
      = .ok (startState.withVm ((startState.evm).set xVar.v_var
          (.Vword .U64 (0xFFFFFFFFFFFFFFFF : BitVec 64))))
    ∧ StateCorrReg [xVar.v_var, yVar.v_var]
        (Store.set st xVar.v_var.vname (t := .reg 64)
          (0xFFFFFFFFFFFFFFFF : BitVec 64))
        ((startState.evm).set xVar.v_var
          (.Vword .U64 (0xFFFFFFFFFFFFFFFF : BitVec 64))) := by
  have h : BitVec.signExtend WSize.U64.bits (0xFFFFFFFF : BitVec 32)
      = (0xFFFFFFFFFFFFFFFF : BitVec 64) := by rfl
  rw [← h]
  exact
    cassgn_signext_selfContained (SyscallState := Unit)
      (Mem := OpSemCoverage.AssignExample.TrivialMem)
      [] .AT_none xVar yVar .U64 .U32 startState st [yVar.v_var]
      (0xFFFFFFFF : BitVec 32)
      (by rfl) (by simp) startState_y
      (by
        intro r' hr'
        rcases List.mem_singleton.mp hr' with h
        subst h
        exact ⟨by decide, by decide⟩)
      hcorr

end SignExtExample

/-! ## §6. Narrowing `Ozeroext` (TRUNC): a worked `x := (u8) y` (`u64 → u8`)

`ComJasminBridgeExt.zextOpSem` produces `BitVec.setWidth szo.bits w`, which
truncates when `szo.bits < szi.bits`. So the landed widening lemmas already cover
narrowing widths: `ComJasminBridgeExt.cassgn_castW_selfContained` is stated for
arbitrary `szo szi`, and instantiating it at `szo < szi` gives the TRUNC bridge
with no distinct unop. Exhibited on `x := (u8) y` (`y : reg u64 = 0x105`,
`x : reg u8 = 5`). -/

namespace TruncExample

/-- `x : reg u8` (the narrowed destination). -/
def xVar : VarI := { v_var := { vname := "x", vtype := .aword .U8 } }
/-- `y : reg u64` (the wide source). -/
def yVar : VarI := { v_var := { vname := "y", vtype := .aword .U64 } }

/-- A start `Estate` holding `y = Vword U64 0x105` (`= 261`; low byte `0x05`). -/
def startState : Estate Unit OpSemCoverage.AssignExample.TrivialMem :=
  { escs := (), emem := (),
    evm := Vm.set Vm.init yVar.v_var (.Vword .U64 (0x105 : BitVec 64)) }

theorem startState_y :
    (startState.evm).get yVar.v_var = .Vword .U64 (0x105 : BitVec 64) := by
  show (Vm.set Vm.init yVar.v_var (.Vword .U64 (0x105 : BitVec 64))).get
        yVar.v_var = _
  simp [Vm.get, Vm.set]

/-- **The narrowed RHS `(u8) y` is DERIVED (not supplied), via truncation.** Given
    an initial `StateCorrReg [y]`, the narrowing `castW` RHS
    `Papp1 (Ozeroext U8 U64) (Pvar y)` *evaluates to* `.ok (.Vword U8 5)` —
    `y`'s `0x105` truncated to its low byte `0x05`, computed from the `Store`
    register `y`. Reuses `ComJasminBridgeExt.papp1_zeroext_read_corr` at
    `szo < szi`. -/
theorem rhs_derived (st : Store)
    (hcorr : StateCorrReg [yVar.v_var] st (startState.evm)) :
    semPexpr (Mem := OpSemCoverage.AssignExample.TrivialMem) true []
        (zextOpSem .U8 .U64) startState
        (.Papp1 (.Ozeroext .U8 .U64) (.Pvar (mkLvar yVar)))
      = .ok (.Vword .U8 (5 : BitVec 8))
    ∧ Store.get st yVar.v_var.vname (.reg 64) = (0x105 : BitVec 64) := by
  obtain ⟨heval, hsy⟩ :=
    papp1_zeroext_read_corr (SyscallState := Unit)
      (Mem := OpSemCoverage.AssignExample.TrivialMem)
      [] startState st [yVar.v_var] yVar .U8 .U64 (0x105 : BitVec 64)
      hcorr (by simp) startState_y
  refine ⟨?_, hsy⟩
  have h : BitVec.setWidth WSize.U8.bits (0x105 : BitVec 64) = (5 : BitVec 8) := by
    rfl
  rw [← h]
  exact heval

/-- **Worked self-contained narrowing `x := (u8) y` step.** From `StateCorrReg [y]`
    with `y = 0x105 : BitVec 64`, the narrowing `castW` `Cassgn` `x := (u8) y`
    mirror-runs to `x = Vword U8 5` — the truncated value **derived** from the
    `Store` register `y` (`ComJasminBridgeExt.papp1_zeroext_read_corr` at
    `szo < szi`), not supplied; and the post-state corresponds
    (`StateCorrReg [x, y]`) to the JasminPrint `Store.set st "x" (5 : BitVec 8)`.
    Reuses `ComJasminBridgeExt.cassgn_castW_selfContained` unchanged. -/
theorem selfContained_truncExample (st : Store)
    (hcorr : StateCorrReg [yVar.v_var] st (startState.evm)) :
    OpSemCoverage.assignExec
        (Mem := OpSemCoverage.AssignExample.TrivialMem) (zextOpSem .U8 .U64) []
        (.Lvar xVar) (.aword .U8)
        (.Papp1 (.Ozeroext .U8 .U64) (.Pvar (mkLvar yVar))) startState
      = .ok (startState.withVm ((startState.evm).set xVar.v_var
          (.Vword .U8 (5 : BitVec 8))))
    ∧ StateCorrReg [xVar.v_var, yVar.v_var]
        (Store.set st xVar.v_var.vname (t := .reg 8) (5 : BitVec 8))
        ((startState.evm).set xVar.v_var (.Vword .U8 (5 : BitVec 8))) := by
  have h : BitVec.setWidth WSize.U8.bits (0x105 : BitVec 64) = (5 : BitVec 8) := by
    rfl
  rw [← h]
  exact
    cassgn_castW_selfContained (SyscallState := Unit)
      (Mem := OpSemCoverage.AssignExample.TrivialMem)
      [] .AT_none xVar yVar .U8 .U64 startState st [yVar.v_var]
      (0x105 : BitVec 64)
      (by rfl) (by simp) startState_y
      (by
        intro r' hr'
        rcases List.mem_singleton.mp hr' with h
        subst h
        exact ⟨by decide, by decide⟩)
      hcorr

end TruncExample

end CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeExt2
