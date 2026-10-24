/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeCmd

/-!
# The last hypothesis of the `Com ↔ Jasmin` bridge: the operand-read correspondence

The `Com ↔ Jasmin` bridge (`ComJasminBridgeFull` / `ComJasminBridgeCmd`) ties the
two reference operational semantics on the register-word `Cassgn`/`regArith`
fragment, but it takes each step's RHS value as a **hypothesis**:

```
hrhs : semPexpr true gd opS s e = .ok (.Vword sz w)
```

i.e. the mirror RHS value `w` is *given*, not *computed from the corresponding
JasminPrint `Store`*. This file **derives** that hypothesis for the `regArith`
emit shape `Papp2 op (Pvar a) (Pvar b)` — the only RHS shape
`InstrRTranslate`'s `regArith` fragment emits (`JasminPrintSemCorrect.lean:140`).
Once derived, the bridge is fully self-contained on the straight-line
`regArith`-`Cassgn` fragment: `hrhs` is a consequence of `StateCorrReg` and the
expression.

## The two reads agree (the central content)

The mirror reads a `Pvar (mkLvar a)` via `getGvar`/`getVar`/`Vm.get`; the
JasminPrint side reads register `a` via `Store.get st a.vname (.reg w)`. Under
`StateCorrReg names st vm`, `RegCorr (st a.vname) (vm.get a)`, i.e.
`st a.vname = encodeRegVal (vm.get a)`. So when `vm.get a = .Vword sz w` the
JasminPrint `Store` holds exactly `⟨reg sz.bits, w⟩` and `Store.get` returns the
*same* `BitVec w`. The two reads are the *same `BitVec`* — `RegCorr` is
near-identity on the reg fragment (`StateBijection`'s central finding). The
read-correspondence is therefore the `Vm.get`/`Store.get` lift of `RegCorr`.

## What is proved (fully proved)

* `pvar_read_corr` — the **variable-read correspondence**: under
  `StateCorrReg names st vm`, if `a ∈ names` reads `vm.get a = .Vword sz w`, then
  the mirror `semPexpr` of `Pvar (mkLvar a)` is `.ok (.Vword sz w)` *and* the
  JasminPrint `Store.get st a.vname (.reg sz.bits) = w`. The two reads agree.
* `papp2_read_corr` — the **`Papp2`-read correspondence**: under `StateCorrReg`,
  `semPexpr` of `Papp2 op (Pvar (mkLvar a)) (Pvar (mkLvar b))` equals
  `opS.sem_sop2 op (.Vword sz wa) (.Vword sz wb)`, with `wa`, `wb` the *Store*
  registers' values — the RHS is computed from the corresponding registers.
* `papp2_word_add_corr` — for a word-add `OpSem` (`addOpSemReg`, matching the
  `regArith .add` emit) the `Papp2` RHS is `.ok (.Vword sz (wa + wb))`: the
  binop of the two Store registers. This **discharges** the bridge's `hrhs`.
* `cassgn_regArith_selfContained` — the **self-contained per-step bridge
  corollary**: `hrhs` is derived, not a hypothesis; for `dst := a + b` over a
  word-add `OpSem`, given both `a, b` live in corresponding registers, the mirror
  run = the JasminPrint `Store.set st dst.vname (wa + wb)`, with the *same*
  `BitVec` the JasminPrint side stores.
* `selfContained_addExample` — the worked `x := y + z` example with the RHS
  **derived** (not supplied): from `StateCorrReg` holding `y`, `z`, the
  `x := y + z` step's RHS value `wy + wz` is computed from the Store, and the
  paired write corresponds.

## Scope

* **Other expression shapes.** This closes the `regArith` RHS shape
  `Papp2 op (Pvar a) (Pvar b)` over register words. The other emit shapes
  (`Papp1 (Ozeroext …)` for `castW`, `Pget` for `stackLoad`, the `Pconst`-folded
  immediate forms used by the `addOpSemW` *constant-folding* examples) are *not*
  covered by `papp2_read_corr` — they need their own read-correspondence
  (`Pconst → .Vint`, the `Ozeroext` unop, the array read). The constant-folding
  `addOpSemW` examples in `ComJasminBridgeFull`/`Cmd` use `Papp2 op (Pvar y)
  (Pconst 1)`, a *mixed* operand shape; this file's `addOpSemReg` instead reads
  *both* operands from registers (`y + z`), the two-register `regArith`
  shape, so the RHS is fully derived from the Store with no folded immediate.
* **Arrays / memory / syscall state.** Out of the reg fragment, as in the scope
  section of `StateBijection`.

`ComJasminBridgeExt`, `ComJasminBridgeExt2` and `ComJasminBridgeArr` supply the
read correspondences for `castW`, sign extension / truncation and the
constant-index `Pget`.

All goals closed.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.OperandReadCorr

open CatCrypt.Crypto.Jasmin.CoqSemMirror
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.StateBijection
open CatCrypt.Crypto.SecureCompilation.VIR.ExecAdequacy
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeFull

variable {SyscallState Mem : Type} [MemModel Mem]

/-! ## §1. The variable-read correspondence

The mirror reads a *local* `Pvar (mkLvar a)` via `getGvar` → (since `mkLvar` has
`isLvar = true`) `getVar true vm a.v_var` → (since a `Vword` is defined)
`.ok (vm.get a.v_var)`. The JasminPrint side reads `Store.get st a.vname
(.reg sz.bits)`. Under `StateCorrReg`, `RegCorr (st a.vname) (vm.get a)`, so when
`vm.get a = .Vword sz w` the `Store` holds `⟨reg sz.bits, w⟩` and both reads
return the same `BitVec`. -/

/-- The mirror reads a local `Pvar` from a `Vword` slot to exactly that `Vword`.
    `getGvar` on an `isLvar` gvar is `getVar`; `getVar true` on a *defined*
    value (a `Vword` is defined) returns it. -/
theorem semPexpr_pvar_vword
    (gd : GlobDecls) (opS : OpSem) (s : Estate SyscallState Mem)
    (a : VarI) (sz : WSize) (w : BitVec sz.bits)
    (hread : (s.evm).get a.v_var = .Vword sz w) :
    semPexpr (Mem := Mem) true gd opS s (.Pvar (mkLvar a))
      = .ok (.Vword sz w) := by
  show getGvar true gd s.evm (mkLvar a) = _
  unfold getGvar
  -- `mkLvar a` is an lvar, so `getGvar = getVar`
  rw [show (mkLvar a).isLvar = true from rfl]
  simp only [ite_true]
  show getVar true s.evm (mkLvar a).gv.v_var = _
  unfold getVar
  -- `(mkLvar a).gv.v_var = a.v_var`, and its value is the defined `Vword`
  rw [show (mkLvar a).gv.v_var = a.v_var from rfl, hread]
  rfl

/-- The JasminPrint `Store` reads the `BitVec` it holds at a `reg`-typed name.
    `Store.get` at the *declared* type returns the stored value. -/
theorem store_get_dynval (st : Store) (name : String) (sz : WSize)
    (w : BitVec sz.bits)
    (hst : st name = (⟨.reg sz.bits, w⟩ : DynVal)) :
    Store.get st name (.reg sz.bits) = w := by
  unfold Store.get
  rw [hst]
  simp

/-- **Variable-read correspondence.** Under `StateCorrReg names st vm`, a register
    `a ∈ names` whose mirror slot holds `Vword sz w`:

    * the mirror `semPexpr` of the local `Pvar a` is `.ok (.Vword sz w)`; and
    * the JasminPrint `Store.get st a.vname (.reg sz.bits)` is the *same* `w`.

    The two reads agree — `RegCorr` is near-identity on the reg fragment. This is
    the operand-read lift of `RegCorr` for one variable. -/
theorem pvar_read_corr
    (gd : GlobDecls) (opS : OpSem) (s : Estate SyscallState Mem) (st : Store)
    (names : List Var) (a : VarI) (sz : WSize) (w : BitVec sz.bits)
    (hcorr : StateCorrReg names st (s.evm))
    (hmem : a.v_var ∈ names)
    (hread : (s.evm).get a.v_var = .Vword sz w) :
    semPexpr (Mem := Mem) true gd opS s (.Pvar (mkLvar a)) = .ok (.Vword sz w)
    ∧ Store.get st a.v_var.vname (.reg sz.bits) = w := by
  refine ⟨semPexpr_pvar_vword gd opS s a sz w hread, ?_⟩
  -- the Store holds the encoding of the mirror value, which is `⟨reg sz.bits, w⟩`
  have hrc : RegCorr (st a.v_var.vname) ((s.evm).get a.v_var) := hcorr a.v_var hmem
  unfold RegCorr at hrc
  rw [hread] at hrc
  -- `encodeRegVal (.Vword sz w) = ⟨reg sz.bits, w⟩`
  have hst : st a.v_var.vname = (⟨.reg sz.bits, w⟩ : DynVal) := hrc
  exact store_get_dynval st a.v_var.vname sz w hst

/-! ## §2. The `Papp2`-read correspondence

`semPexpr` of `Papp2 op e1 e2` evaluates `e1`, then `e2`, then applies
`opS.sem_sop2`. For the `regArith` shape both `e1`, `e2` are local `Pvar`s, so by
§1 they reduce to the two register `Vword`s read from the corresponding Store
slots, and the whole expression is `opS.sem_sop2 op (.Vword sz wa) (.Vword sz wb)`
— computed from the Store registers' values. -/

/-- **`Papp2`-read correspondence.** Under `StateCorrReg`, with both operands
    `a, b ∈ names` reading register `Vword`s `wa`, `wb`, the mirror
    `semPexpr (Papp2 op (Pvar a) (Pvar b))` reduces to applying `opS.sem_sop2` to
    the two register words — and those words are exactly what the JasminPrint
    `Store` holds at `a`, `b` (by `pvar_read_corr`). The RHS is *computed from the
    corresponding registers*, not supplied. -/
theorem papp2_read_corr
    (gd : GlobDecls) (opS : OpSem) (s : Estate SyscallState Mem) (st : Store)
    (names : List Var) (op : SOp2) (a b : VarI) (sz : WSize)
    (wa wb : BitVec sz.bits)
    (hcorr : StateCorrReg names st (s.evm))
    (hma : a.v_var ∈ names) (hmb : b.v_var ∈ names)
    (hra : (s.evm).get a.v_var = .Vword sz wa)
    (hrb : (s.evm).get b.v_var = .Vword sz wb) :
    semPexpr (Mem := Mem) true gd opS s
        (.Papp2 op (.Pvar (mkLvar a)) (.Pvar (mkLvar b)))
      = opS.sem_sop2 op (.Vword sz wa) (.Vword sz wb)
    ∧ Store.get st a.v_var.vname (.reg sz.bits) = wa
    ∧ Store.get st b.v_var.vname (.reg sz.bits) = wb := by
  obtain ⟨hea, hsa⟩ := pvar_read_corr gd opS s st names a sz wa hcorr hma hra
  obtain ⟨heb, hsb⟩ := pvar_read_corr gd opS s st names b sz wb hcorr hmb hrb
  refine ⟨?_, hsa, hsb⟩
  show (do
      let v1 ← semPexpr (Mem := Mem) true gd opS s (.Pvar (mkLvar a))
      let v2 ← semPexpr (Mem := Mem) true gd opS s (.Pvar (mkLvar b))
      opS.sem_sop2 op v1 v2) = _
  rw [hea, heb]
  rfl

/-! ## §3. The word-add `OpSem` discharge

For a register word-add `OpSem` (`addOpSemReg`, the two-register analogue of
`ComJasminBridgeFull.addOpSemW` — but reading *both* operands from registers,
matching the `regArith .add` emit), the `Papp2` RHS is `.ok (.Vword sz (wa + wb))`
— the `BitVec` add of the two Store registers. This is exactly the bridge's
`hrhs`, now *derived*. -/

/-- A register word-add `OpSem`: `Oadd (Op_w sz)` adds the two register words.
    This is the two-register `regArith .add` semantics — both operands come from
    registers (no constant fold), matching `JasminBinOp.apply .add` on the
    `Com.denote` side. -/
def addOpSemReg (sz : WSize) : OpSem where
  sem_sop1 := fun _ _ => .typeError
  sem_sop2 := fun
    | .Oadd (.Op_w sz'), .Vword sz'' a, .Vword _ b =>
        if h : sz' = sz ∧ sz'' = sz then
          .ok (.Vword sz ((h.2 ▸ a) + (by
            -- the second operand's width also matches `sz`
            -- (forced by the `Papp2` reading two same-`sz` registers); we
            -- re-tag defensively via `BitVec.ofNat`
            exact BitVec.ofNat sz.bits b.toNat)))
        else .typeError
    | _, _, _ => .typeError
  sem_opN := fun _ _ => .typeError

/-- **Word-add `OpSem` on two matching-width registers gives the `BitVec` add.**
    `addOpSemReg sz` applied to two `Vword sz` words returns `.ok (.Vword sz
    (wa + wb))`. -/
theorem addOpSemReg_sem (sz : WSize) (wa wb : BitVec sz.bits) :
    (addOpSemReg sz).sem_sop2 (.Oadd (.Op_w sz)) (.Vword sz wa) (.Vword sz wb)
      = .ok (.Vword sz (wa + wb)) := by
  show (if h : sz = sz ∧ sz = sz then
          (.ok (.Vword sz ((h.2 ▸ wa) + BitVec.ofNat sz.bits wb.toNat)) : JResult Value)
        else .typeError) = _
  rw [dite_eq_left ⟨rfl, rfl⟩]
  have hbv : BitVec.ofNat sz.bits wb.toNat = wb := by
    apply BitVec.eq_of_toNat_eq; simp
  rw [hbv]

/-- **The discharged RHS (word add).** Under `StateCorrReg`, for the word-add
    `OpSem` the `regArith` RHS `Papp2 (Oadd (Op_w sz)) (Pvar a) (Pvar b)`
    *evaluates to* `.ok (.Vword sz (wa + wb))`, where `wa`, `wb` are the values
    the JasminPrint `Store` holds at `a`, `b`. This is the bridge's `hrhs`,
    derived from the operand reads rather than assumed. -/
theorem papp2_word_add_corr
    (gd : GlobDecls) (s : Estate SyscallState Mem) (st : Store)
    (names : List Var) (a b : VarI) (sz : WSize)
    (wa wb : BitVec sz.bits)
    (hcorr : StateCorrReg names st (s.evm))
    (hma : a.v_var ∈ names) (hmb : b.v_var ∈ names)
    (hra : (s.evm).get a.v_var = .Vword sz wa)
    (hrb : (s.evm).get b.v_var = .Vword sz wb) :
    semPexpr (Mem := Mem) true gd (addOpSemReg sz) s
        (.Papp2 (.Oadd (.Op_w sz)) (.Pvar (mkLvar a)) (.Pvar (mkLvar b)))
      = .ok (.Vword sz (wa + wb))
    ∧ Store.get st a.v_var.vname (.reg sz.bits) = wa
    ∧ Store.get st b.v_var.vname (.reg sz.bits) = wb := by
  obtain ⟨heval, hsa, hsb⟩ :=
    papp2_read_corr gd (addOpSemReg sz) s st names (.Oadd (.Op_w sz)) a b sz
      wa wb hcorr hma hmb hra hrb
  refine ⟨?_, hsa, hsb⟩
  rw [heval, addOpSemReg_sem]

/-! ## §4. The self-contained per-step bridge corollary

The bridge's per-step lemma `cassgn_regArith_simulates` took `hrhs` as a
hypothesis. Here we *derive* it from `StateCorrReg` + the `regArith` RHS, then
feed it through, getting a bridge step whose RHS value is computed — not
supplied. -/

/-- **Self-contained per-step bridge (word add, RHS derived).** For
    `dst := a + b` (register `u`-words, word-add `OpSem`), given:

    * `dst` is a register of width `sz`, frame-distinct from `names`;
    * both source registers `a, b ∈ names` hold `Vword sz wa`, `Vword sz wb`;
    * the states correspond (`StateCorrReg names`),

    the mirror `Cassgn` run lands `s.withVm (s.evm.set dst (.Vword sz (wa + wb)))`,
    and the post-state corresponds (`StateCorrReg (dst :: names)`) to the
    JasminPrint `Store.set st dst.vname (wa + wb)` — the *same* `BitVec` the
    JasminPrint `regArith .add` produces from the corresponding registers. The
    RHS value `wa + wb` is **derived** from the operand reads
    (`papp2_word_add_corr`), not assumed. -/
theorem cassgn_regArith_selfContained
    (gd : GlobDecls) (tag : AssgnTag)
    (dst a b : VarI) (sz : WSize)
    (s : Estate SyscallState Mem) (st : Store) (names : List Var)
    (wa wb : BitVec sz.bits)
    (hdst : dst.v_var.vtype = .aword sz)
    (hma : a.v_var ∈ names) (hmb : b.v_var ∈ names)
    (hra : (s.evm).get a.v_var = .Vword sz wa)
    (hrb : (s.evm).get b.v_var = .Vword sz wb)
    (hdistinct : ∀ r' ∈ names, r' ≠ dst.v_var ∧ r'.vname ≠ dst.v_var.vname)
    (hcorr : StateCorrReg names st (s.evm)) :
    OpSemCoverage.assignExec (Mem := Mem) (addOpSemReg sz) gd (.Lvar dst)
        (.aword sz)
        (.Papp2 (.Oadd (.Op_w sz)) (.Pvar (mkLvar a)) (.Pvar (mkLvar b))) s
      = .ok (s.withVm ((s.evm).set dst.v_var (.Vword sz (wa + wb))))
    ∧ StateCorrReg (dst.v_var :: names)
        (Store.set st dst.v_var.vname (t := .reg sz.bits) (wa + wb))
        ((s.evm).set dst.v_var (.Vword sz (wa + wb))) := by
  -- derive the RHS value from the corresponding registers
  obtain ⟨hrhs, _, _⟩ :=
    papp2_word_add_corr gd s st names a b sz wa wb hcorr hma hmb hra hrb
  -- feed the *derived* `hrhs` into the bridge's per-step simulation lemma
  exact cassgn_regArith_simulates (SyscallState := SyscallState) (Mem := Mem)
    gd (addOpSemReg sz) dst sz tag
    (.Papp2 (.Oadd (.Op_w sz)) (.Pvar (mkLvar a)) (.Pvar (mkLvar b)))
    (wa + wb) s st names hdst hrhs hdistinct hcorr

/-! ## §5. Worked `x := y + z` example, RHS derived

We exhibit the two-register `regArith` add `x := y + z` (register
`u32`), with the RHS value *computed from the Store* (`y`, `z` both read from
corresponding registers), not supplied as a constant. -/

namespace AddExample

/-- `x : reg u32`. -/
def xVar : VarI := { v_var := { vname := "x", vtype := .aword .U32 } }
/-- `y : reg u32`. -/
def yVar : VarI := { v_var := { vname := "y", vtype := .aword .U32 } }
/-- `z : reg u32`. -/
def zVar : VarI := { v_var := { vname := "z", vtype := .aword .U32 } }

/-- A start `Estate` holding `y = Vword U32 5`, `z = Vword U32 2`. -/
def startState : Estate Unit OpSemCoverage.AssignExample.TrivialMem :=
  { escs := (), emem := (),
    evm := Vm.set (Vm.set Vm.init yVar.v_var (.Vword .U32 (5 : BitVec 32)))
              zVar.v_var (.Vword .U32 (2 : BitVec 32)) }

theorem startState_y :
    (startState.evm).get yVar.v_var = .Vword .U32 (5 : BitVec 32) := by
  show (Vm.set (Vm.set Vm.init yVar.v_var (.Vword .U32 (5 : BitVec 32)))
          zVar.v_var (.Vword .U32 (2 : BitVec 32))).get yVar.v_var = _
  simp [Vm.get, Vm.set]; decide

theorem startState_z :
    (startState.evm).get zVar.v_var = .Vword .U32 (2 : BitVec 32) := by
  show (Vm.set (Vm.set Vm.init yVar.v_var (.Vword .U32 (5 : BitVec 32)))
          zVar.v_var (.Vword .U32 (2 : BitVec 32))).get zVar.v_var = _
  simp [Vm.get, Vm.set]

/-- **The RHS `y + z` is DERIVED (not supplied).** Given an initial
    `StateCorrReg [y, z]`, the `regArith` RHS `Papp2 (Oadd (Op_w U32)) (Pvar y)
    (Pvar z)` *evaluates to* `.ok (.Vword U32 7)` — `5 + 2 = 7` computed from the
    `Store` registers `y`, `z`, with the JasminPrint Store reads pinned to the
    same `5`, `2`. -/
theorem rhs_derived (st : Store)
    (hcorr : StateCorrReg [yVar.v_var, zVar.v_var] st (startState.evm)) :
    semPexpr (Mem := OpSemCoverage.AssignExample.TrivialMem) true []
        (addOpSemReg .U32)
        startState
        (.Papp2 (.Oadd (.Op_w .U32)) (.Pvar (mkLvar yVar)) (.Pvar (mkLvar zVar)))
      = .ok (.Vword .U32 (7 : BitVec 32))
    ∧ Store.get st yVar.v_var.vname (.reg 32) = (5 : BitVec 32)
    ∧ Store.get st zVar.v_var.vname (.reg 32) = (2 : BitVec 32) := by
  obtain ⟨heval, hsy, hsz⟩ :=
    papp2_word_add_corr (SyscallState := Unit)
      (Mem := OpSemCoverage.AssignExample.TrivialMem)
      [] startState st [yVar.v_var, zVar.v_var] yVar zVar .U32
      (5 : BitVec 32) (2 : BitVec 32) hcorr
      (by simp) (by simp) startState_y startState_z
  refine ⟨?_, hsy, hsz⟩
  -- `5 + 2 = 7` over `BitVec 32` (definitional after the derived `heval`)
  rw [heval]; rfl

/-- **Worked self-contained `x := y + z` step.** From `StateCorrReg [y, z]` with
    `y = 5`, `z = 2`, the `regArith` `Cassgn` `x := y + z`:

    * mirror-runs to `x = Vword U32 7` — the RHS value `7` **derived** from the
      Store registers (`papp2_word_add_corr`), not supplied; and
    * the post-state corresponds (`StateCorrReg [x, y, z]`) to the JasminPrint
      `Store.set st "x" (7 : BitVec 32)` — the same `7`.

    This is the fully self-contained per-step bridge: no `hrhs` hypothesis, the
    RHS value is computed from the corresponding registers. -/
theorem selfContained_addExample (st : Store)
    (hcorr : StateCorrReg [yVar.v_var, zVar.v_var] st (startState.evm)) :
    OpSemCoverage.assignExec
        (Mem := OpSemCoverage.AssignExample.TrivialMem) (addOpSemReg .U32) []
        (.Lvar xVar) (.aword .U32)
        (.Papp2 (.Oadd (.Op_w .U32)) (.Pvar (mkLvar yVar)) (.Pvar (mkLvar zVar)))
        startState
      = .ok (startState.withVm ((startState.evm).set xVar.v_var
          (.Vword .U32 (7 : BitVec 32))))
    ∧ StateCorrReg [xVar.v_var, yVar.v_var, zVar.v_var]
        (Store.set st xVar.v_var.vname (t := .reg 32) (7 : BitVec 32))
        ((startState.evm).set xVar.v_var (.Vword .U32 (7 : BitVec 32))) := by
  -- `5 + 2 = 7` over `BitVec 32` is definitional, so the bridge instance has the
  -- post-state `x = 7` already (no manual rewrite needed).
  exact
    cassgn_regArith_selfContained (SyscallState := Unit)
      (Mem := OpSemCoverage.AssignExample.TrivialMem)
      [] .AT_none xVar yVar zVar .U32 startState st [yVar.v_var, zVar.v_var]
      (5 : BitVec 32) (2 : BitVec 32)
      (by rfl) (by simp) (by simp) startState_y startState_z
      (by
        intro r' hr'
        rcases List.mem_cons.mp hr' with h | h
        · subst h; exact ⟨by decide, by decide⟩
        · rcases List.mem_singleton.mp h with h; subst h
          exact ⟨by decide, by decide⟩)
      hcorr

end AddExample

end CatCrypt.Crypto.SecureCompilation.VIR.OperandReadCorr
