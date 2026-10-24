/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.OperandReadCorr

/-!
# `Com ↔ Jasmin` bridge extension: the `castW` (width-cast) expression shape

`ComJasminBridgeFull` / `ComJasminBridgeCmd` land the per-step and whole-command
bridge for the register-word `Cassgn`/`regArith` fragment; `OperandReadCorr`
makes the two-register `Papp2` add self-contained by *deriving* the RHS value
from the corresponding `Store`. Its scope note names the next shape:

> The other emit shapes (`Papp1 (Ozeroext …)` for `castW`, `Pget` for
> `stackLoad`, …) are *not* covered by `papp2_read_corr` — they need their own
> read-correspondence (the `Ozeroext` unop, the array read).

This file closes the **`castW`** one: the width-cast expression shape
`Papp1 (Ozeroext szo szi) (Pvar a)`, the RHS `InstrRTranslate`'s `castW` binding
emits (`JasminDialect.castW _ w'` denotes `(a).zeroExtend w'`). It is a
mechanical port of the `Papp2` operand-read correspondence: the mirror
`semPexpr` of a `Papp1 (Ozeroext szo szi)` over a `Pvar` reads the source
register through `pvar_read_corr` (the same `RegCorr` near-identity) and applies
the zero-extension unop, and the value it produces is `BitVec.setWidth szo.bits`
of the source word — exactly the `Com.denote` of `castW szi szo`
(`(a).zeroExtend szo.bits`).

## The `castW` operand semantics

`castW`'s mirror unop is `SOp1.Ozeroext szo szi` (`operators.v` mirror). We model
its `OpSem` (`zextOpSem`) so that on a `Vword szi w` it returns
`Vword szo (BitVec.setWidth szo.bits w)` — the widening zero-extension. The
`Com` side (`JasminDialect.jasminDenote`) denotes `castW _ w'` as
`(args.head).zeroExtend w'`; `BitVec.zeroExtend` *is* `BitVec.setWidth`, so the
two carry the *same* `BitVec` (`castW_denote_eq_setWidth`).

## What is proved (fully proved)

* `zextOpSem` / `zextOpSem_sem` — the width-cast unop `OpSem` and its evaluation
  on a matching-width word: `Vword szi w ↦ Vword szo (setWidth szo.bits w)`.
* `castW_denote_eq_setWidth` — the `Com.denote` of `castW szi szo` on `w` is the
  *same* `BitVec.setWidth szo.bits w` the mirror unop produces (value coincidence
  with the compiler side).
* `semPexpr_papp1_zeroext` — the mirror `semPexpr` of `Papp1 (Ozeroext szo szi)
  (Pvar a)` when `a` reads `Vword szi w`: `.ok (Vword szo (setWidth szo.bits w))`.
* `papp1_zeroext_read_corr` — the **`castW`-read correspondence** (the
  `Papp1`-analogue of `papp2_read_corr`): under `StateCorrReg`, the mirror
  `Papp1 (Ozeroext szo szi) (Pvar a)` evaluates to the widened source word, and
  the JasminPrint `Store.get st a (.reg szi.bits)` is the *same* source `w`.
* `cassgn_castW_selfContained` — the **self-contained per-step `castW` bridge**:
  for `dst := (Ozeroext szo szi) a` (destination register `aword szo`), given `a`
  in a corresponding register holding `Vword szi w`, the mirror `Cassgn` run
  lands `s.withVm (s.evm.set dst (Vword szo (setWidth szo.bits w)))` and the
  post-state corresponds (`StateCorrReg (dst :: names)`) to the JasminPrint
  `Store.set st dst (setWidth szo.bits w)` — the same `BitVec` the `Com.denote`
  `castW` produces. The RHS value is *derived* (via `papp1_zeroext_read_corr`),
  not assumed. Threads through `ComJasminBridgeFull.cassgn_regArith_simulates`
  (generic in the RHS expression `e` and value `w`).
* `cassgn_castW_endToEnd` — adds adequacy: the run *witnesses* the reference
  `psem.v` relational step `SemIr` (via `ComJasminBridgeFull.cassgn_regArith_endToEnd`).
* `WidenExample.selfContained_widenExample` — the worked `x := (u64) y` example
  (`y : reg u32 = 5 ↦ x : reg u64 = 5`), RHS derived from the `Store`.

## Scope

This closes the `castW` RHS shape `Papp1 (Ozeroext szo szi) (Pvar a)` at the
semantic (mirror + `Store`) level — the operand-read correspondence and the
self-contained per-step + end-to-end bridge, mirroring `OperandReadCorr`'s
`papp2` development. The narrowing `Ozeroext` (`szo < szi`, i.e. `TRUNC`) and the
signed `Osignext` unops, and the `Pget`/`stackLoad` array read, remain their own
shapes (the same residuals the bridge files catalogue). The AST-translation
extension of `InstrRTranslate` (adding a `translateSOp1` + `Papp1` case) is a
separate mechanical addition to that file; this file supplies the
read-correspondence the per-step bridge consumes.

All goals closed.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeExt

open CatCrypt.Crypto.Jasmin.CoqSemMirror
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.StateBijection
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeFull
open CatCrypt.Crypto.SecureCompilation.VIR.OperandReadCorr

variable {SyscallState Mem : Type} [MemModel Mem]

/-! ## §1. The width-cast unop `OpSem`

`castW`'s mirror unop is `SOp1.Ozeroext szo szi` — zero-extend the input word
(width `szi`) to the output width `szo`. We model its `OpSem` so that on a
matching-width `Vword szi w` it returns `Vword szo (BitVec.setWidth szo.bits w)`,
the widening. Other input shapes are type errors (out of the reg fragment). -/

/-- The width-cast (`castW`) `OpSem`: `Ozeroext szo szi` on a `Vword szi w`
    returns the zero-extended `Vword szo (BitVec.setWidth szo.bits w)`. Both
    widths are checked against the operator's tags (defensive `if`, as in
    `OperandReadCorr.addOpSemReg`). -/
def zextOpSem (szo szi : WSize) : OpSem where
  sem_sop1 := fun
    | .Ozeroext szo' _szi', .Vword sz'' w =>
        if h : szo' = szo ∧ sz'' = szi then
          .ok (.Vword szo (BitVec.setWidth szo.bits (h.2 ▸ w)))
        else .typeError
    | _, _ => .typeError
  sem_sop2 := fun _ _ _ => .typeError
  sem_opN := fun _ _ => .typeError

/-- **The width-cast unop evaluates to the zero-extension.** `zextOpSem szo szi`
    applied to `Ozeroext szo szi` and a matching-width `Vword szi w` returns
    `.ok (.Vword szo (BitVec.setWidth szo.bits w))`. -/
theorem zextOpSem_sem (szo szi : WSize) (w : BitVec szi.bits) :
    (zextOpSem szo szi).sem_sop1 (.Ozeroext szo szi) (.Vword szi w)
      = .ok (.Vword szo (BitVec.setWidth szo.bits w)) := by
  show (if h : szo = szo ∧ szi = szi then
          (.ok (.Vword szo (BitVec.setWidth szo.bits (h.2 ▸ w))) : JResult Value)
        else .typeError) = _
  rw [dite_eq_left ⟨rfl, rfl⟩]

/-- **`Com`/mirror value coincidence.** The `Com.denote` of `JasminDialect.castW
    szi szo` on `w` (`(w).zeroExtend szo.bits`) is the *same* `BitVec` the mirror
    width-cast unop produces (`BitVec.setWidth szo.bits w`) — `BitVec.zeroExtend`
    is definitionally `BitVec.setWidth`. -/
theorem castW_denote_eq_setWidth (szo szi : WSize) (w : BitVec szi.bits) :
    (w.zeroExtend szo.bits) = BitVec.setWidth szo.bits w := rfl

/-! ## §2. The `castW` operand-read correspondence

The mirror `semPexpr` of `Papp1 (Ozeroext szo szi) (Pvar a)` evaluates the
operand `Pvar a` (via `OperandReadCorr.semPexpr_pvar_vword`) to the source word,
then applies the width-cast unop. Under `StateCorrReg`, the source word is
exactly what the JasminPrint `Store` holds at `a` (`pvar_read_corr`), so the two
reads agree and the widened result is derived — not supplied. -/

/-- The mirror `semPexpr` of `Papp1 (Ozeroext szo szi) (Pvar a)`, when `a` reads
    `Vword szi w`, is `.ok (.Vword szo (BitVec.setWidth szo.bits w))`. Composes
    `OperandReadCorr.semPexpr_pvar_vword` (operand read) with `zextOpSem_sem`
    (the width-cast unop). -/
theorem semPexpr_papp1_zeroext
    (gd : GlobDecls) (s : Estate SyscallState Mem)
    (a : VarI) (szo szi : WSize) (w : BitVec szi.bits)
    (hread : (s.evm).get a.v_var = .Vword szi w) :
    semPexpr (Mem := Mem) true gd (zextOpSem szo szi) s
        (.Papp1 (.Ozeroext szo szi) (.Pvar (mkLvar a)))
      = .ok (.Vword szo (BitVec.setWidth szo.bits w)) := by
  show (do
      let v1 ← semPexpr (Mem := Mem) true gd (zextOpSem szo szi) s (.Pvar (mkLvar a))
      (zextOpSem szo szi).sem_sop1 (.Ozeroext szo szi) v1) = _
  rw [semPexpr_pvar_vword gd (zextOpSem szo szi) s a szi w hread]
  exact zextOpSem_sem szo szi w

/-- **`castW`-read correspondence.** Under `StateCorrReg names st vm`, for a
    source register `a ∈ names` reading `Vword szi w`:

    * the mirror `semPexpr` of `Papp1 (Ozeroext szo szi) (Pvar a)` is
      `.ok (.Vword szo (BitVec.setWidth szo.bits w))` — the widened source; and
    * the JasminPrint `Store.get st a.vname (.reg szi.bits)` is the *same* source
      word `w`.

    The RHS value is *computed from the corresponding register*, not supplied.
    The `Papp1`-analogue of `OperandReadCorr.papp2_read_corr`. -/
theorem papp1_zeroext_read_corr
    (gd : GlobDecls) (s : Estate SyscallState Mem) (st : Store)
    (names : List Var) (a : VarI) (szo szi : WSize) (w : BitVec szi.bits)
    (hcorr : StateCorrReg names st (s.evm))
    (hmem : a.v_var ∈ names)
    (hread : (s.evm).get a.v_var = .Vword szi w) :
    semPexpr (Mem := Mem) true gd (zextOpSem szo szi) s
        (.Papp1 (.Ozeroext szo szi) (.Pvar (mkLvar a)))
      = .ok (.Vword szo (BitVec.setWidth szo.bits w))
    ∧ Store.get st a.v_var.vname (.reg szi.bits) = w := by
  refine ⟨semPexpr_papp1_zeroext gd s a szo szi w hread, ?_⟩
  exact (pvar_read_corr gd (zextOpSem szo szi) s st names a szi w hcorr hmem hread).2

/-! ## §3. The self-contained per-step `castW` bridge

The bridge's per-step lemma `ComJasminBridgeFull.cassgn_regArith_simulates` is
generic in the RHS expression `e` and its value `w` (it takes `hrhs` as a
hypothesis). We *derive* `hrhs` for the `castW` shape from
`papp1_zeroext_read_corr` and feed it through: the destination width is the
*output* width `szo`, and the produced value is the widened source. -/

/-- **Self-contained per-step `castW` bridge (RHS derived).** For
    `dst := (Ozeroext szo szi) a` (destination register of width `szo`), given:

    * `dst` is a register of width `szo`, frame-distinct from `names`;
    * the source register `a ∈ names` holds `Vword szi w`;
    * the states correspond (`StateCorrReg names`),

    the mirror `Cassgn` run lands
    `s.withVm (s.evm.set dst (.Vword szo (BitVec.setWidth szo.bits w)))`, and the
    post-state corresponds (`StateCorrReg (dst :: names)`) to the JasminPrint
    `Store.set st dst.vname (BitVec.setWidth szo.bits w)` — the *same* `BitVec`
    the `Com.denote` `castW szi szo` produces (`castW_denote_eq_setWidth`). The
    RHS value is derived from the operand read, not assumed. -/
theorem cassgn_castW_selfContained
    (gd : GlobDecls) (tag : AssgnTag)
    (dst a : VarI) (szo szi : WSize)
    (s : Estate SyscallState Mem) (st : Store) (names : List Var)
    (w : BitVec szi.bits)
    (hdst : dst.v_var.vtype = .aword szo)
    (hmem : a.v_var ∈ names)
    (hread : (s.evm).get a.v_var = .Vword szi w)
    (hdistinct : ∀ r' ∈ names, r' ≠ dst.v_var ∧ r'.vname ≠ dst.v_var.vname)
    (hcorr : StateCorrReg names st (s.evm)) :
    OpSemCoverage.assignExec (Mem := Mem) (zextOpSem szo szi) gd (.Lvar dst)
        (.aword szo)
        (.Papp1 (.Ozeroext szo szi) (.Pvar (mkLvar a))) s
      = .ok (s.withVm ((s.evm).set dst.v_var
          (.Vword szo (BitVec.setWidth szo.bits w))))
    ∧ StateCorrReg (dst.v_var :: names)
        (Store.set st dst.v_var.vname (t := .reg szo.bits)
          (BitVec.setWidth szo.bits w))
        ((s.evm).set dst.v_var (.Vword szo (BitVec.setWidth szo.bits w))) := by
  obtain ⟨hrhs, _⟩ :=
    papp1_zeroext_read_corr gd s st names a szo szi w hcorr hmem hread
  exact cassgn_regArith_simulates (SyscallState := SyscallState) (Mem := Mem)
    gd (zextOpSem szo szi) dst szo tag
    (.Papp1 (.Ozeroext szo szi) (.Pvar (mkLvar a)))
    (BitVec.setWidth szo.bits w) s st names hdst hrhs hdistinct hcorr

/-! ## §4. The end-to-end `castW` bridge (adequacy)

Chaining `ComJasminBridgeFull.cassgn_regArith_endToEnd` on top: the mirror run
of the translated `castW` `Cassgn` *witnesses* the reference `psem.v` relational
step `SemIr`, and the post-state corresponds. -/

/-- **End-to-end per-step `castW` bridge.** For the `castW` `Cassgn`
    `dst := (Ozeroext szo szi) a`, at fuel `fuel+1`:

    * **(adequacy)** the mirror executor run *witnesses* the reference relational
      step `SemIr` landing `s.withVm (s.evm.set dst (.Vword szo (setWidth …)))`; and
    * **(state bijection)** the post-state corresponds (`StateCorrReg`) to the
      JasminPrint `Store.set st dst.vname (setWidth szo.bits w)` — the write the
      `Com.denote` `castW` side performs with the same `BitVec`.

    The RHS value is derived from the operand read (`papp1_zeroext_read_corr`). -/
theorem cassgn_castW_endToEnd
    (aS : AsmSem) (gd : GlobDecls) (prog : Prog)
    (dst a : VarI) (szo szi : WSize) (tag : AssgnTag)
    (s : Estate SyscallState Mem) (st : Store) (names : List Var) (fuel : Nat)
    (w : BitVec szi.bits)
    (hdst : dst.v_var.vtype = .aword szo)
    (hmem : a.v_var ∈ names)
    (hread : (s.evm).get a.v_var = .Vword szi w)
    (hdistinct : ∀ r' ∈ names, r' ≠ dst.v_var ∧ r'.vname ≠ dst.v_var.vname)
    (hcorr : StateCorrReg names st (s.evm)) :
    SemIr (Mem := Mem) aS (zextOpSem szo szi) gd prog s
        (.Cassgn (.Lvar dst) tag (.aword szo)
          (.Papp1 (.Ozeroext szo szi) (.Pvar (mkLvar a))))
        (s.withVm ((s.evm).set dst.v_var (.Vword szo (BitVec.setWidth szo.bits w))))
    ∧ StateCorrReg (dst.v_var :: names)
        (Store.set st dst.v_var.vname (t := .reg szo.bits)
          (BitVec.setWidth szo.bits w))
        ((s.evm).set dst.v_var (.Vword szo (BitVec.setWidth szo.bits w))) := by
  obtain ⟨hrhs, _⟩ :=
    papp1_zeroext_read_corr gd s st names a szo szi w hcorr hmem hread
  exact cassgn_regArith_endToEnd (SyscallState := SyscallState) (Mem := Mem)
    aS (zextOpSem szo szi) gd prog dst szo tag
    (.Papp1 (.Ozeroext szo szi) (.Pvar (mkLvar a)))
    (BitVec.setWidth szo.bits w) s st names fuel hdst hrhs hdistinct hcorr

/-! ## §5. Worked example: `x := (u64) y` (`reg u32 → reg u64` widen)

The width-cast `x := (u64) y` (`y : reg u32`, `x : reg u64`), with the
RHS value *computed from the `Store`* (`y` read from a corresponding register),
not supplied. From `y = 5 : BitVec 32` the widened result is `5 : BitVec 64`. -/

namespace WidenExample

/-- `x : reg u64` (the widened destination). -/
def xVar : VarI := { v_var := { vname := "x", vtype := .aword .U64 } }
/-- `y : reg u32` (the narrow source). -/
def yVar : VarI := { v_var := { vname := "y", vtype := .aword .U32 } }

/-- A start `Estate` holding `y = Vword U32 5`. -/
def startState : Estate Unit OpSemCoverage.AssignExample.TrivialMem :=
  { escs := (), emem := (),
    evm := Vm.set Vm.init yVar.v_var (.Vword .U32 (5 : BitVec 32)) }

theorem startState_y :
    (startState.evm).get yVar.v_var = .Vword .U32 (5 : BitVec 32) := by
  show (Vm.set Vm.init yVar.v_var (.Vword .U32 (5 : BitVec 32))).get yVar.v_var = _
  simp [Vm.get, Vm.set]

/-- **The widened RHS `(u64) y` is DERIVED (not supplied).** Given an initial
    `StateCorrReg [y]`, the `castW` RHS `Papp1 (Ozeroext U64 U32) (Pvar y)`
    *evaluates to* `.ok (.Vword U64 5)` — `y`'s `5 : BitVec 32` zero-extended to
    `BitVec 64`, computed from the `Store` register `y`. -/
theorem rhs_derived (st : Store)
    (hcorr : StateCorrReg [yVar.v_var] st (startState.evm)) :
    semPexpr (Mem := OpSemCoverage.AssignExample.TrivialMem) true []
        (zextOpSem .U64 .U32) startState
        (.Papp1 (.Ozeroext .U64 .U32) (.Pvar (mkLvar yVar)))
      = .ok (.Vword .U64 (5 : BitVec 64))
    ∧ Store.get st yVar.v_var.vname (.reg 32) = (5 : BitVec 32) := by
  obtain ⟨heval, hsy⟩ :=
    papp1_zeroext_read_corr (SyscallState := Unit)
      (Mem := OpSemCoverage.AssignExample.TrivialMem)
      [] startState st [yVar.v_var] yVar .U64 .U32 (5 : BitVec 32)
      hcorr (by simp) startState_y
  refine ⟨?_, hsy⟩
  have h5 : BitVec.setWidth WSize.U64.bits (5 : BitVec 32) = (5 : BitVec 64) := by
    rfl
  rw [← h5]
  exact heval

/-- **Worked self-contained `x := (u64) y` step.** From `StateCorrReg [y]` with
    `y = 5 : BitVec 32`, the `castW` `Cassgn` `x := (u64) y`:

    * mirror-runs to `x = Vword U64 5` — the widened value **derived** from the
      `Store` register `y` (`papp1_zeroext_read_corr`), not supplied; and
    * the post-state corresponds (`StateCorrReg [x, y]`) to the JasminPrint
      `Store.set st "x" (5 : BitVec 64)` — the same `BitVec` the `Com.denote`
      `castW U32 U64` produces (`castW_denote_eq_setWidth`).

    The fully self-contained per-step `castW` bridge: no `hrhs` hypothesis, the
    RHS value is computed from the corresponding register. -/
theorem selfContained_widenExample (st : Store)
    (hcorr : StateCorrReg [yVar.v_var] st (startState.evm)) :
    OpSemCoverage.assignExec
        (Mem := OpSemCoverage.AssignExample.TrivialMem) (zextOpSem .U64 .U32) []
        (.Lvar xVar) (.aword .U64)
        (.Papp1 (.Ozeroext .U64 .U32) (.Pvar (mkLvar yVar))) startState
      = .ok (startState.withVm ((startState.evm).set xVar.v_var
          (.Vword .U64 (5 : BitVec 64))))
    ∧ StateCorrReg [xVar.v_var, yVar.v_var]
        (Store.set st xVar.v_var.vname (t := .reg 64) (5 : BitVec 64))
        ((startState.evm).set xVar.v_var (.Vword .U64 (5 : BitVec 64))) := by
  have h5 : BitVec.setWidth WSize.U64.bits (5 : BitVec 32) = (5 : BitVec 64) := by
    rfl
  rw [← h5]
  exact
    cassgn_castW_selfContained (SyscallState := Unit)
      (Mem := OpSemCoverage.AssignExample.TrivialMem)
      [] .AT_none xVar yVar .U64 .U32 startState st [yVar.v_var]
      (5 : BitVec 32)
      (by rfl) (by simp) startState_y
      (by
        intro r' hr'
        rcases List.mem_singleton.mp hr' with h
        subst h
        exact ⟨by decide, by decide⟩)
      hcorr

end WidenExample

end CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeExt
