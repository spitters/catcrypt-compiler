/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresGeneric
public import CatCrypt.Crypto.SecureCompilation.RelationalCompile
public import CatCrypt.Crypto.SecureCompilation.ScalarLinX86Demo

/-!
# The descent's `Refines` as an ascent correspondence at the x86 machine

The relational compiler certifies a `Com jasminDialect` fragment builder `frag`
against a Lean state step `spec : View 64 → View 64` by `Refines spec frag`.
Closing the fragment with the returning continuation `retSlot dst` gives a closed
`Com`; the de Bruijn front `comToRegProg` flattens it, the x86 `ScalarTarget`
compiles it, and `com_x86_e2e` reads the compiled block's result register back as
`Com.denote`. This module composes the two into a forward simulation from the
machine state to the readout view: the abstract state is the `View 64`, the
abstract step is `spec`.

The front binds every result to a fresh register, so the register holding a
written slot differs between entry and exit, and no single state relation is an
invariant of the block. `CorresMPost` carries one relation at entry (`SRview`:
the register file is the de Bruijn reflection `envOf` of a valuation whose
readout is the view) and another at exit (`SRret`: the result register holds
slot `dst` of the view); `CorresM` is its diagonal.

The x86 `ScalarTarget` runs `xrun` over `X86Backend.Model.State`, a different
machine from the `runBlock` of `CorresJ`, so the bridge is stated as a
`CorresMPost` at the step `xrunStep`.

## Main definitions

* `retSlot`, `descentCom` — the returning continuation and the closed fragment
* `refines_ret` — `Refines` at the returning continuation
* `CorresMPost` — the forward simulation with distinct entry and exit relations
* `SRview`, `SRret` — the entry and exit relations, generic in the machine
* `corresMPost_of_readout` — the machine-generic bridge
* `corres_of_refines_x86` — the bridge at `xrunStep`
* `twoArgEnv`, `twoArgVal`, `binFrag`, `descentSubCom` — a two-argument word kernel
  through the descent
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.Sha2Emit
open CatCrypt.Crypto.SecureCompilation.VIR.Sha2EmitterReduction
open CatCrypt.Crypto.SecureCompilation.RelationalCompile
open CatCrypt.Crypto.SecureCompilation.ScalarLin
open CatCrypt.Crypto.SecureCompilation.ScalarLinFront
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
open CatCrypt.Crypto.SecureCompilation.ScalarLinX86Demo

/-! ## 1. The descent contract at the return -/

/-- The continuation returning slot `j` of the environment it is handed. -/
def retSlot (w : Nat) (j : Nat) : SCont w (Rw w) := fun e => Com.ret (e.slot j)

/-- A fragment builder over width `w`, returning a `reg w` value. -/
abbrev Frag (w : Nat) : Type :=
  {Γ : Ctxt jasminDialect} → Env w Γ → SCont w (Rw w) → Com jasminDialect Γ (Rw w)

/-- The fragment closed with `retSlot j`: a closed `Com` returning slot `j`. -/
def descentCom {w : Nat} {Γ : Ctxt jasminDialect} (frag : Frag w) (e : Env w Γ) (j : Nat) :
    Com jasminDialect Γ (Rw w) :=
  frag e (retSlot w j)

/-- A fragment closed with `retSlot j` denotes to slot `j` of the spec's output
    view. The `Refines` analogue of `frefines_ret`. -/
theorem refines_ret {w : Nat} {spec : StateStep w} {frag : Frag w} (h : Refines spec frag)
    {Γ : Ctxt jasminDialect} (e : Env w Γ) (V : Ctxt.Valuation Γ) (j : Nat) :
    (descentCom frag e j).denote V = (spec (readView e V)).slot j := by
  obtain ⟨Γ', envF, VF, hden, hview⟩ := h e V (retSlot w j)
  rw [descentCom, hden, ← hview]
  rfl

/-! ## 2. The forward simulation with distinct entry and exit relations -/

/-- From a machine state related by `SRin` to an abstract state satisfying `P`,
    the step makes progress to a state related by `SRout` to the abstract result.
    `CorresM` is the diagonal `SRin = SRout`. -/
def CorresMPost {M C AState : Type} (step : C → M → Option M)
    (SRin SRout : M → AState → Prop) (P : AState → Prop) (fa : AState → AState)
    (c : C) : Prop :=
  ∀ m a, SRin m a → P a → ∃ m', step c m = some m' ∧ SRout m' (fa a)

/-- `CorresM` is `CorresMPost` on the diagonal. -/
theorem corresM_eq_corresMPost {M C AState : Type} (step : C → M → Option M)
    (SR : M → AState → Prop) (P : AState → Prop) (fa : AState → AState) (c : C) :
    CorresM step SR P fa c = CorresMPost step SR SR P fa c := rfl

/-- The entry relation: the register file is the de Bruijn reflection `envOf` of a
    valuation whose readout through `e` is the view. -/
def SRview {M : Type} (regs : M → String → BitVec 64) {Γ : Ctxt jasminDialect}
    (e : Env 64 Γ) (m : M) (vw : View 64) : Prop :=
  ∃ V : Ctxt.Valuation Γ, regs m = envOf Γ.length V ∧ readView e V = vw

/-- The exit relation: register `r` holds slot `dst` of the view. -/
def SRret {M : Type} (regs : M → String → BitVec 64) (r : String) (dst : Nat)
    (m : M) (vw : View 64) : Prop :=
  regs m r = vw.slot dst

/-- The machine-generic bridge. A descent result `Refines spec frag` and a readout
    theorem for the compiled block `c` (from a state reflecting `V`, the step lands
    in a state whose register `r` holds the closed fragment's denotation at `V`)
    give the forward simulation from `SRview` to `SRret` at the abstract step
    `spec`. -/
theorem corresMPost_of_readout {M C : Type} (step : C → M → Option M)
    (regs : M → String → BitVec 64) {Γ : Ctxt jasminDialect} (e : Env 64 Γ)
    {spec : StateStep 64} {frag : Frag 64} (h : Refines spec frag) (dst : Nat)
    (c : C) (r : String)
    (hrun : ∀ (V : Ctxt.Valuation Γ) (m : M), regs m = envOf Γ.length V →
      ∃ m', step c m = some m' ∧ regs m' r = (descentCom frag e dst).denote V) :
    CorresMPost step (SRview regs e) (SRret regs r dst) (fun _ => True) spec c := by
  intro m vw hin _
  obtain ⟨V, hm, hvw⟩ := hin
  obtain ⟨m', hstep, hr⟩ := hrun V m hm
  refine ⟨m', hstep, ?_⟩
  show regs m' r = (spec vw).slot dst
  rw [hr, refines_ret h e V dst, hvw]

/-! ## 3. The x86 bridge -/

/-- The x86 `ScalarTarget` run `xrun` as a never-failing step, the `runBlockStep`
    twin over `X86Backend.Model.State`. -/
def xrunStep (ops : List XInstr) (s : XState) : Option XState := some (xrun s ops)

/-- **The x86 bridge.** From a descent result `Refines spec frag`, the compiled
    x86 block of the fragment closed at slot `dst` is a forward simulation at the
    abstract step `spec`: entered from a state reflecting a valuation whose readout
    is the view, it exits with the result register `comRetName` holding slot `dst`
    of `spec` applied to the view. The side conditions are those of `com_x86_e2e`:
    the closed fragment is in the supported straight-line fragment (`ComOK`), the
    context is all `reg 64`, and every compiled shift amount is in range. -/
theorem corres_of_refines_x86 {Γ : Ctxt jasminDialect} (hΓ : AllReg64 Γ) (e : Env 64 Γ)
    {spec : StateStep 64} {frag : Frag 64} (h : Refines spec frag) (dst : Nat)
    (hok : ComOK (descentCom frag e dst))
    (hsh : ∀ stmt ∈ comToRegProg (descentCom frag e dst) Γ.length, ShiftAmtOK stmt) :
    CorresMPost xrunStep (SRview (fun s : XState => s.regs) e)
      (SRret (fun s : XState => s.regs) (comRetName (descentCom frag e dst) Γ.length) dst)
      (fun _ => True) spec
      (x86Target.compile (comToRegProg (descentCom frag e dst) Γ.length)) :=
  corresMPost_of_readout xrunStep (fun s : XState => s.regs) e h dst _ _ fun V s hs =>
    ⟨_, rfl, com_x86_e2e hok hΓ V s hs hsh⟩

/-! ## 4. A two-argument word kernel through the descent

A Lean function `fun a b : BitVec 64 => op.apply a b` reaches the descent as the
fragment `binFrag op`, one `emitOp` writing slot `0` from the two inputs. Over the
two-argument context `[reg 64, reg 64]`, `twoArgEnv` places input `0` at de Bruijn
level `0` (register `v0`, the first argument) and input `1` at level `1` (register
`v1`, the second). -/

/-- The environment of a two-argument kernel: input `i` is argument `i`; every
    slot is parked at the second argument's variable until it is written. -/
def twoArgEnv : Env 64 [.reg 64, .reg 64] where
  slot _ := .here
  inp i := if i = 0 then .there .here else .here

/-- The valuation of the two-argument context with argument `a` at level `0` and
    `b` at level `1`. -/
def twoArgVal (a b : BitVec 64) : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect) :=
  .cons b (.cons a .nil)

/-- The fragment of a binary word operation on the two inputs, writing slot `0`. -/
def binFrag (op : JasminBinOp) : Frag 64 :=
  fun e k => emitOp e op 0 (.iw 0) (.iw 1) k

/-- The `Com` the descent produces for `fun a b : BitVec 64 => a - b`: `binFrag .sub`
    closed at slot `0` over `twoArgEnv`. -/
def descentSubCom : Com jasminDialect [.reg 64, .reg 64] (.reg 64) :=
  descentCom (binFrag .sub) twoArgEnv 0

/-- `binFrag op` refines the one-slot arithmetic step. -/
theorem binFrag_refines (op : JasminBinOp) :
    Refines (arithStep op 0 (.iw 0) (.iw 1)) (binFrag op) :=
  Refines.arith op 0 (.iw 0) (.iw 1)

/-- The closed two-argument kernel is in the supported straight-line fragment
    whenever its op is. -/
theorem binCom_ok (op : JasminBinOp) (hop : SupportedOp (.regArith op 64)) :
    ComOK (descentCom (binFrag op) twoArgEnv 0) :=
  ComOK.var hop (ComOK.ret _)

/-- The flattened two-argument kernel is the single statement `v2 := v0 op v1`
    for the six ALU ops, and empty otherwise. -/
theorem binCom_flatten (op : JasminBinOp) :
    comToRegProg (descentCom (binFrag op) twoArgEnv 0) 2
      = opToStmts (lvlName 2) [lvlName 0, lvlName 1] (.regArith op 64) := by
  simp only [descentCom, binFrag, emitOp, comToRegProg_var, retSlot, comToRegProg_ret,
    List.append_nil]
  rfl

/-- A `regArith` op never flattens to a shift statement. -/
theorem opToStmts_regArith_shiftOK (bop : JasminBinOp) (dst : String) (srcs : List String) :
    ∀ stmt ∈ opToStmts dst srcs (.regArith bop 64), ShiftAmtOK stmt := by
  intro stmt hstmt
  cases bop <;>
    (rcases srcs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp_all [opToStmts, ShiftAmtOK])

/-- The two-argument kernel compiles to shift-free statements. -/
theorem binCom_shiftOK (op : JasminBinOp) :
    ∀ stmt ∈ comToRegProg (descentCom (binFrag op) twoArgEnv 0) 2, ShiftAmtOK stmt := by
  rw [binCom_flatten]
  exact opToStmts_regArith_shiftOK op _ _

/-- Slot `0` of the arithmetic step, read from `twoArgVal a b`, is `op.apply a b`. -/
theorem binStep_readout (op : JasminBinOp) (a b : BitVec 64) :
    (arithStep op 0 (.iw 0) (.iw 1) (readView twoArgEnv (twoArgVal a b))).slot 0
      = op.apply a b := rfl

end CatCrypt.Crypto.SecureCompilation.Ascent
