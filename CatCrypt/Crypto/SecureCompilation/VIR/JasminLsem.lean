/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-!
# A faithful Lean model of jasmin's linear semantics `lsem` — increment 1

This module is **increment 1** of porting jasmin's `proofs/lang/linear_sem.v`
(`lsem`/`lsem1`/`eval_instr`) to Lean. It provides the *semantics-foundation*
half of the Com→`lsem` faithfulness predicate `ComLsemExportFaithful`
(`LsemPortAll`): the Lean model of jasmin's `lsem` over which that predicate is
stated and proved. This file provides that model **for the straight-line
fragment**.

## Scope of increment 1 (honest statement)

Increment 1 models, *faithfully*, only the **straight-line** `linstr_r` cases —
the ones whose Coq `eval_instr` semantics do not consult the program label table
or transfer control:

* `Lopn xs o es`  — the assignment/word-op case. In Coq:
  `eval_instr (Lopn xs o es) s = ... ok (lnext_pc (lset_estate' s1 s'))`, i.e.
  evaluate the source `rexprs`, run `exec_sopn o`, write the destination
  `lexprs`, and advance the pc by one. We model the word-op fragment of
  `exec_sopn` (the `JasminBinOp` images that `JasminLprogExport.binOpName`
  produces, plus immediate `MOV` and the ABI 64-bit move `MOVQ` the
  prologue/arg-materialization/epilogue emit), which is exactly the subset
  `Com.toLprog` / `comToLfundefPhysAbi` emit.
* `Lalign`     — Coq `ok (lnext_pc s1)` (pc bump only).
* `Llabel _ _` — Coq `ok (lnext_pc s1)` (pc bump only; a label declaration is a
  no-op for the store, only relevant as a `find_label` target for control flow).
* `Lret` (the function-return terminator) — modeled by `lsemRun` (§6), which
  *ends* a whole-function straight-line run at the trailing `Lret`
  (`comToBody_ends_Lret`) returning the current `Lstate`, the state `lfd_res` is
  read off. The single-step `lsemStep .Lret` stays `none` (it is genuine control
  flow at the instruction level); the terminator semantics live in the
  whole-function fold `lsemRun`, which agrees with `lsemStraight` on the
  `Lret`-free body prefix (`lsemRun_eq_lsemStraight` / `lsemRun_body_ret`).

**Out of scope for increment 1** (control flow / effects — modeled as `none`,
*not* faked): `Lgoto`, `Lcond`, `Ligoto`, `Lcall`, `LstoreLabel`, `Lsyscall`.
Each of these in Coq calls `eval_jump`/`find_label`/`rencode_label`/
`exec_syscall`, i.e. it reads the whole-program label table `label_in_lprog` or
the syscall oracle. Modeling them faithfully needs the program `P`, the label
machinery (`find_label`, `eval_jump`), and the memory/syscall effects — that is
**increment 2/3**. Here their `lsemStep` is honestly `none` ("not modeled in
the straight-line foundation"), never a fabricated step.

## What increment 2 will need

Increment 2 — the simulation `Com.denote com = lsem (Com.toLprog com) ∘ encode`
— will need, on top of this foundation:
* the program-indexed `find_instr`/`step` of Coq (a `Section`-`Context (P :
  lprog)`): `lsemStep` here is the *instruction-local* `eval_instr`; the
  program-level `step s = eval_instr (find_instr s) s` adds `lp_funcs`/`lpc`
  lookup, which `lsemStraight` below already specialises for the straight-line
  case (the fold over a fundef body);
* `eval_jump`/`find_label` for the control-flow cases;
* a value encoding `encode : ⟦Γ⟧ → lvm` matching `JasminLprogExport`'s
  `regName`/`argName` register naming, and the agreement
  `Com.denote = lsem ∘ toLprog ∘ encode`.

## Fidelity / modeling choices (trust-critical)

The Lean `lstate` here mirrors the three Coq `lstate` fields that the
straight-line fragment touches — `lvm` (the var map), `lmem` (memory), and
`lpc` (program counter) — and drops the two that only control-flow / syscalls
use (`lscs` syscall state, `lfn` current function name; the latter only indexes
`find_instr`, which `lsemStraight` folds away). The store `lvm` is modeled at a
single uniform word width `w` (`String → BitVec w`), matching the uniform-width
straight-line word kernels and the existing `X86Backend.Jasmin.JState.regs`
register file (the linear straight-line machine is the *same shape* as
`JState`/`runBlock`; the agreement of this `lsem` with that `runBlock` is **not**
proved in increment 1). `lsemStep` for `Lopn` is faithful to `eval_instr`'s
`Lopn` arm on the modeled opcodes: the destination is written with
`applyOpn opn (srcs.map eval)` and the pc is advanced by one (`lnext_pc`).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. `lstate`: the linear-machine state (straight-line fields)

Mirror of Coq `Record lstate := Lstate { lscs ; lmem ; lvm ; lfn ; lpc }`
restricted to the fields the straight-line fragment reads/writes. -/

/-- The linear-machine state for the straight-line fragment, at a uniform word
    width `w`. Mirrors the `lvm`/`lmem`/`lpc` fields of jasmin's `lstate`
    (`linear_sem.v` l.41–46). The dropped Coq fields (`lscs`, `lfn`) are only
    used by the out-of-scope control-flow / syscall cases. -/
structure Lstate (w : Nat) where
  /-- `lvm : Vm.t` — the variable/register map. Modeled at uniform width `w`
      (`String → BitVec w`), the same shape as `X86Backend.Jasmin.JState.regs`. -/
  lvm : String → BitVec w
  /-- `lmem : mem` — word-addressed memory `(base, byte-offset) ↦ word`
      (same shape as `X86Backend.Jasmin.JMem`). Untouched cells read `0`. -/
  lmem : String → Int → BitVec w := fun _ _ => 0
  /-- `lpc : nat` — the program counter. -/
  lpc : Nat := 0

/-- `setpc`/`lnext_pc` analogue: read a register from `lvm`. Absent ⇒ `0`. -/
@[simp] def Lstate.get {w : Nat} (s : Lstate w) (r : String) : BitVec w := s.lvm r

/-- Write a register, leaving memory and the pc unchanged. The `lvm`-update of
    `lset_estate'` (`linear_sem.v` l.53–54) restricted to a single var write. -/
def Lstate.setReg {w : Nat} (s : Lstate w) (r : String) (v : BitVec w) : Lstate w :=
  { s with lvm := fun r' => if r' = r then v else s.lvm r' }

/-- `lnext_pc s = setpc s (lpc s).+1` (`linear_sem.v` l.64–65): advance the pc by
    one, leaving the store and memory unchanged. -/
def Lstate.nextPc {w : Nat} (s : Lstate w) : Lstate w := { s with lpc := s.lpc + 1 }

@[simp] theorem Lstate.lvm_setReg {w : Nat} (s : Lstate w) (r : String) (v : BitVec w) :
    (s.setReg r v).lvm = (fun r' => if r' = r then v else s.lvm r') := rfl

@[simp] theorem Lstate.lpc_setReg {w : Nat} (s : Lstate w) (r : String) (v : BitVec w) :
    (s.setReg r v).lpc = s.lpc := rfl

@[simp] theorem Lstate.get_setReg_same {w : Nat} (s : Lstate w) (r : String)
    (v : BitVec w) : (s.setReg r v).get r = v := by simp [Lstate.setReg, Lstate.get]

@[simp] theorem Lstate.get_setReg_other {w : Nat} (s : Lstate w) (r r' : String)
    (v : BitVec w) (h : r' ≠ r) : (s.setReg r v).get r' = s.get r' := by
  simp [Lstate.setReg, Lstate.get, h]

@[simp] theorem Lstate.lpc_nextPc {w : Nat} (s : Lstate w) : s.nextPc.lpc = s.lpc + 1 := rfl

@[simp] theorem Lstate.lvm_nextPc {w : Nat} (s : Lstate w) : s.nextPc.lvm = s.lvm := rfl

/-! ## 2. Operand evaluation and the word-op fragment of `exec_sopn`

`eval_instr`'s `Lopn` arm runs `sem_rexprs s es` then `exec_sopn o args`. We
evaluate the `LOperand` sources against `lvm`/`lmem` and apply the textual
opcode `opn`. The modeled opcode set is exactly the `JasminBinOp` image that
`JasminLprogExport.binOpName` produces (plus immediate `MOV`) — the subset
`Com.toLprog` emits for the word-level two-address fragment. -/

/-- `sem_rexpr` for the surface `LOperand` shapes: a register reads `lvm`, an
    immediate is a literal, an array element / SIB element reads `lmem`
    (`base`, offset). Faithful to `sem_rexpr` on the `Pvar`/`Pconst`/`Pload`
    cases the export emits. -/
def evalOperand {w : Nat} (s : Lstate w) : LOperand → BitVec w
  | .reg r => s.lvm r
  | .imm v => BitVec.ofNat w v
  | .arr base idx => s.lmem base (Int.ofNat idx)
  | .arrIdx base idx scale =>
      -- SIB element `base[idx*scale]`: effective offset is `scale · ⟦idx⟧`.
      s.lmem base (Int.ofNat (scale * (s.lvm idx).toNat))

/-- The modeled word-op fragment of `exec_sopn`: map a *stripped* (width-tag
    removed) mnemonic and the evaluated source words to the result word, when the
    opcode is one we model. This is the `JasminBinOp.apply` image of
    `JasminLprogExport.binOpName` (binary register arithmetic) plus the immediate
    `MOV` (a `regConst`/`castW` nullary/unary move) and the ABI `MOVQ` (the
    64-bit register/memory move the prologue/arg-materialization/epilogue emit;
    same word semantics as `MOV`).

    Returns `none` for any opcode outside the modeled straight-line word
    fragment (e.g. `MULXHI`, `CALL:…`, `LOAD`/`STORE`, `CMOV`) — honest
    partiality, not a default value. -/
def applyOpn {w : Nat} : String → List (BitVec w) → Option (BitVec w)
  | "ADD", [a, b] => some (a + b)
  | "SUB", [a, b] => some (a - b)
  | "MUL", [a, b] => some (a * b)
  | "AND", [a, b] => some (a &&& b)
  | "OR",  [a, b] => some (a ||| b)
  | "XOR", [a, b] => some (a ^^^ b)
  | "SHL", [a, b] => some (a <<< b.toNat)
  | "SHR", [a, b] => some (a >>> b.toNat)
  | "ANDN", [a, b] => some ((~~~a) &&& b)
  | "MOV", [a] => some a
  -- `MOVQ`: the 64-bit register/memory move the ABI prologue, arg-pointer
  -- materialization, and epilogue emit (`buildPrologue`/`buildArgPtrMaterialize`/
  -- `buildEpilogue`/`calleeSaveRestoreEpilogue`). Identical word semantics to
  -- `MOV` (copy the single evaluated source word); only the asm-printer width
  -- and the `read_linear.ml` mnemonic differ. The source/destination spread —
  -- reg←reg, reg←[mem/qsave slot], [mem]←reg — is handled by `evalOperand`/
  -- `setReg` reading/writing the `.reg`-named cells (memory cells are rendered
  -- via `LOperand.reg (memName …)` / `"qsave.…"`, so they are uniform `lvm`
  -- entries at this model's granularity).
  | "MOVQ", [a] => some a
  | _, _ => none

/-- `applyOpn` agrees with `JasminBinOp.apply` (the dialect denotation) on the
    binary register-arithmetic opcodes that `binOpName` produces. This is the
    fidelity tie between the `lsem` word-op model and the dialect semantics that
    `Com.toLprog` lowers from. -/
theorem applyOpn_binOpName {w : Nat} (bop : JasminBinOp) (a b : BitVec w) :
    applyOpn (binOpName bop) [a, b] = some (bop.apply a b) := by
  cases bop <;> rfl

/-- The ABI `MOVQ` opcode copies its single source word unchanged — the fidelity
    tie for the 64-bit move the prologue/arg-materialization/epilogue emit (same
    word semantics as `MOV`). -/
@[simp] theorem applyOpn_MOVQ {w : Nat} (a : BitVec w) :
    applyOpn "MOVQ" [a] = some a := rfl

/-- `MOVQ` carries no `":64"` width tag, so `stripWidthTag` leaves it unchanged —
    the body mnemonic the `lsemStep` `Lopn` arm recovers it as. -/
@[simp] theorem stripWidthTag_MOVQ : stripWidthTag "MOVQ" = "MOVQ" := by
  decide +kernel

/-- `MOVQ` and `MOV` denote the same word op (a pure copy). -/
theorem applyOpn_MOVQ_eq_MOV {w : Nat} (a : BitVec w) :
    applyOpn "MOVQ" [a] = applyOpn "MOV" [a] := rfl

/-! ## 3. `lsemStep` / `lsem1`: the single-instruction step

Mirror of Coq `eval_instr (i : linstr) (s1 : lstate) : exec lstate`
(`linear_sem.v` l.112–173), restricted to the straight-line cases. Coq's `exec`
monad is `result error`; we use `Option` (the partiality), with `none` for both
"genuine error" (a modeled op applied to ill-typed args) and "out of scope"
(control-flow cases). The distinction is documented per-arm. -/

/-- The single-step linear semantics for one `LinstrR`, faithful to Coq
    `eval_instr` on the straight-line cases:

    * `Lopn [dst] opn srcs` — evaluate `srcs` against the store, apply the
      modeled `applyOpn` opcode, write `dst`, and advance the pc
      (`lnext_pc (lset_estate' …)`). `none` if the opcode is unmodeled or the
      arity is wrong (Coq's `exec_sopn` type error) or there is not exactly one
      destination.
    * `Lalign` — `ok (lnext_pc s1)` (pc bump only).
    * `Llabel _ _` — `ok (lnext_pc s1)` (pc bump only).

    Control-flow / effect cases (`Lgoto`/`Lcond`/`Ligoto`/`Lcall`/`Lret`/
    `LstoreLabel`/`Lsyscall`) are **out of scope** for increment 1 and return
    `none` — they are not modeled, not faked (see module docstring). -/
def lsemStep {w : Nat} (i : LinstrR) (s : Lstate w) : Option (Lstate w) :=
  match i with
  | .Lopn [.reg dst] opn srcs =>
      match applyOpn (stripWidthTag opn) (srcs.map (evalOperand s)) with
      | some v => some ((s.setReg dst v).nextPc)
      | none => none
  | .Lopn _ _ _ => none
  | .Lalign => some s.nextPc
  | .Llabel _ _ => some s.nextPc
  -- Out of scope for increment 1 (control flow / effects): not modeled.
  | .Lgoto _ => none
  | .Lcond _ _ => none
  | .Ligoto _ => none
  | .Lcall _ _ => none
  | .Lret => none
  | .LstoreLabel _ _ => none
  | .Lsyscall _ => none

/-- `lsem1` (Coq `Definition lsem1 s1 s2 := step s1 = ok s2`, l.180–181) as a
    relation, here instruction-local: `lsem1 i s1 s2` holds iff stepping
    instruction `i` from `s1` yields `s2`. (The program-level `step` that fetches
    `i` via `find_instr` is folded into `lsemStraight` below for the
    straight-line case.) -/
def lsem1 {w : Nat} (i : LinstrR) (s1 s2 : Lstate w) : Prop := lsemStep i s1 = some s2

/-- `lsem1` is deterministic — the linear step is a function (Coq `lsem1_fun`,
    `linear_sem.v` l.226–232). Immediate from `lsemStep` being a function. -/
theorem lsem1_deterministic {w : Nat} (i : LinstrR) (s1 s2 s3 : Lstate w)
    (h12 : lsem1 i s1 s2) (h13 : lsem1 i s1 s3) : s2 = s3 := by
  rw [lsem1] at h12 h13; rw [h12] at h13; exact Option.some.inj h13

/-! ### 3a. Per-op `MOVQ` step lemmas (ABI prologue / arg-materialization / epilogue)

The ABI wrapper (`buildPrologue`, `buildArgPtrMaterialize`, `buildEpilogue`,
`calleeSaveRestoreEpilogue`) emits, exclusively, single-source `MOVQ`s of the
shape `Lopn [.reg dst] "MOVQ" [src]`. Mirroring the `MOV` step behaviour, each
writes `dst := evalOperand s src` and advances the pc. The three named lemmas
below cover the operand shapes those builders use: a register source
(reg←reg / the qsave-slot copies), a memory/stack-slot source rendered as
`LOperand.reg (memName …)` (reg←[mem], the load side), and a register source
written to a memory/stack cell rendered as `LOperand.reg (memName …)`
([mem]←reg, the store side). Because memory cells are rendered as `.reg`-named
`lvm` entries at this model's granularity, all three reduce to the same uniform
register-copy step — exactly the `MOV` single-arg arm with mnemonic `"MOVQ"`. -/

/-- **General `MOVQ` step.** Running `Lopn [.reg dst] "MOVQ" [src]` writes
    `evalOperand s src` to `dst` and advances the pc — the `Lopn` arm of
    `eval_instr` on the `"MOVQ"` opcode. The single faithful step the ABI
    prologue/arg-materialization/epilogue rely on. -/
theorem lsemStep_movq {w : Nat} (dst : String) (src : LOperand) (s : Lstate w) :
    lsemStep (.Lopn [.reg dst] "MOVQ" [src]) s
      = some ((s.setReg dst (evalOperand s src)).nextPc) := by
  simp only [lsemStep, stripWidthTag_MOVQ, List.map_cons, List.map_nil, applyOpn_MOVQ]

/-- `MOVQ` reg←reg (the `qsave.*` saves/restores and ABI-register copies): writes
    `s.lvm src` to `dst`, pc bumped. -/
theorem movq_reg_lsem {w : Nat} (dst src : String) (s : Lstate w) :
    lsemStep (.Lopn [.reg dst] "MOVQ" [.reg src]) s
      = some ((s.setReg dst (s.lvm src)).nextPc) := by
  rw [lsemStep_movq]; rfl

/-- `MOVQ` reg←[mem]: a load whose source is a memory/stack cell rendered as
    `LOperand.reg (memName base off)`. Writes the cell's `lvm` value to `dst`,
    pc bumped. (`memName base off` is just a `.reg` name at this model's
    granularity, so this is the same uniform copy as `movq_reg_lsem`.) -/
theorem movq_load_lsem {w : Nat} (dst memCell : String) (s : Lstate w) :
    lsemStep (.Lopn [.reg dst] "MOVQ" [.reg memCell]) s
      = some ((s.setReg dst (s.lvm memCell)).nextPc) := by
  rw [lsemStep_movq]; rfl

/-- `MOVQ` [mem]←reg: a store whose destination is a memory/stack cell rendered
    as `LOperand.reg (memName base off)`. Writes the source register's value to
    the cell, pc bumped (same uniform copy, destination is the cell name). -/
theorem movq_store_lsem {w : Nat} (memCell src : String) (s : Lstate w) :
    lsemStep (.Lopn [.reg memCell] "MOVQ" [.reg src]) s
      = some ((s.setReg memCell (s.lvm src)).nextPc) := by
  rw [lsemStep_movq]; rfl

/-! ## 4. `lsemStraight`: the straight-line multi-step execution

Coq's `lsem` is `clos_refl_trans lstate lsem1` (the reflexive-transitive
closure, l.183) over the program-level `step` that re-fetches the instruction at
`lpc` from `lp_funcs`. For **straight-line** code (no jumps, no labels redirecting
control), executing the fundef body is exactly the sequential left fold of
`lsemStep` over the body's instructions, advancing the pc by one each time —
which is what every modeled arm does (`lnext_pc`). `lsemStraight` is that fold;
it is the restriction of `lsem` to straight-line bodies (the analogue of
`X86Backend.Jasmin.runBlock`, but over the linear IR and threading the pc). -/

/-- Straight-line execution of a list of `LinstrR`: the sequential fold of
    `lsemStep`, short-circuiting to `none` at the first unmodeled / erroring
    instruction. This is the reflexive-transitive closure `lsem` restricted to
    straight-line code (each step advances the pc by one). -/
def lsemStraight {w : Nat} : List LinstrR → Lstate w → Option (Lstate w)
  | [], s => some s
  | i :: is, s =>
      match lsemStep i s with
      | some s' => lsemStraight is s'
      | none => none

@[simp] theorem lsemStraight_nil {w : Nat} (s : Lstate w) :
    lsemStraight [] s = some s := rfl

@[simp] theorem lsemStraight_cons {w : Nat} (i : LinstrR) (is : List LinstrR)
    (s : Lstate w) :
    lsemStraight (i :: is) s =
      (match lsemStep i s with
        | some s' => lsemStraight is s'
        | none => none) := rfl

/-- A single modeled instruction `lsemStraight`-steps to its `lsemStep` image. -/
theorem lsemStraight_singleton {w : Nat} (i : LinstrR) (s : Lstate w) :
    lsemStraight [i] s = lsemStep i s := by
  simp only [lsemStraight]
  cases lsemStep i s <;> rfl

/-! ## 5. The proved structural law: sequential composition (`lsem_trans`)

The straight-line analogue of Coq `lsem_trans` (`linear_sem.v` l.212–214,
transitivity of `clos_refl_trans`): running `xs ++ ys` is running `xs` then
running `ys` from the resulting state. Stated in `Option`-Kleisli form so it
holds unconditionally (both the success and the short-circuit-to-`none` cases).
This is the law a `Com.toLprog` simulation peels by (one binding at a time). -/

/-- **Sequential composition** of straight-line execution: `lsemStraight` of a
    concatenation is the Kleisli composite of the two halves. The increment-1
    characterising law (faithful straight-line restriction of `lsem_trans`).
    Sorry-free, proved by induction on the prefix. -/
theorem lsemStraight_append {w : Nat} (xs ys : List LinstrR) (s : Lstate w) :
    lsemStraight (xs ++ ys) s = (lsemStraight xs s).bind (lsemStraight ys) := by
  induction xs generalizing s with
  | nil => simp
  | cons i is ih =>
      simp only [List.cons_append, lsemStraight]
      cases lsemStep i s with
      | none => rfl
      | some s' => exact ih s'

/-- `lsemStraight` is deterministic (a function): immediate, since it is defined
    as a function. The straight-line analogue of the fact that `lsem` composed
    of the deterministic `lsem1` has a unique terminating state. -/
theorem lsemStraight_deterministic {w : Nat} (is : List LinstrR) (s t1 t2 : Lstate w)
    (h1 : lsemStraight is s = some t1) (h2 : lsemStraight is s = some t2) : t1 = t2 := by
  rw [h1] at h2; exact Option.some.inj h2

/-! ## 6. `lsemRun`: whole-function execution with the `Lret` terminator

`lsemStraight` is the body-block fold; it short-circuits to `none` at any
unmodeled instruction, including the function-return `Lret` (because
`lsemStep .Lret = none`). A *whole function* body, however, is exactly a
straight-line `Lret`-free prefix followed by the single trailing `Lret` the
linearizer always emits (`JasminLprogExport.comToBody_ends_Lret`). `lsemRun`
models that: run the body up to the `Lret`, and *terminate* at the `Lret`
returning the current `Lstate` (jasmin's `eval_instr (Lret) s` transfers control
out of the fundef; for the straight-line whole-function model the observation
`lfd_res` is read off this returned state). Instructions after the `Lret` are
unreachable and dropped. This is the additive `Lret`-handling layer over
`lsemStraight` that the whole-function `toLprogPhysAbi_lsem_goal` runs against;
`lsemStraight`'s own equations are unchanged. -/

/-- Whole-function straight-line execution: like `lsemStraight`, but the
    function-return terminator `Lret` *ends* the run and returns the current
    state (instead of `lsemStraight`'s `none`-on-`Lret`). Every modeled
    non-`Lret` instruction steps via `lsemStep`; an unmodeled instruction still
    short-circuits to `none`. -/
def lsemRun {w : Nat} : List LinstrR → Lstate w → Option (Lstate w)
  | [], s => some s
  | i :: is, s =>
      match i with
      | .Lret => some s
      | i =>
        match lsemStep i s with
        | some s' => lsemRun is s'
        | none => none

@[simp] theorem lsemRun_nil {w : Nat} (s : Lstate w) :
    lsemRun [] s = some s := rfl

/-- `lsemRun` terminates at a leading `Lret`, returning the current state — the
    whole-function return semantics (`comToBody_ends_Lret`). -/
@[simp] theorem lsemRun_cons_Lret {w : Nat} (is : List LinstrR) (s : Lstate w) :
    lsemRun (.Lret :: is) s = some s := rfl

/-- `lsemRun` cons-steps any **non-`Lret`** head via `lsemStep`, exactly like
    `lsemStraight`. -/
theorem lsemRun_cons {w : Nat} (i : LinstrR) (is : List LinstrR) (s : Lstate w)
    (h : i ≠ .Lret) :
    lsemRun (i :: is) s =
      (match lsemStep i s with
        | some s' => lsemRun is s'
        | none => none) := by
  cases i <;> first | rfl | exact absurd rfl h

/-- On a `Lret`-free instruction list, `lsemRun` agrees with `lsemStraight`
    (there is no terminator to short-circuit on, so both folds coincide). The
    bridge that lets the existing `lsemStraight`-based body/prologue simulation
    lemmas be reused inside a `lsemRun` whole-function run. -/
theorem lsemRun_eq_lsemStraight {w : Nat} (is : List LinstrR) (s : Lstate w)
    (h : .Lret ∉ is) : lsemRun is s = lsemStraight is s := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih =>
      have hi : i ≠ .Lret := fun he => h (he ▸ List.mem_cons_self ..)
      have hmem : .Lret ∉ is := fun hm => h (List.mem_cons_of_mem _ hm)
      rw [lsemRun_cons _ _ _ hi, lsemStraight_cons]
      cases lsemStep i s with
      | none => rfl
      | some s' => exact ih s' hmem

/-- **Whole-function decomposition**: running a `Lret`-free body prefix `body`
    followed by the trailing `Lret` (and any unreachable tail `rest`) with
    `lsemRun` is exactly running `body` with `lsemStraight` and reading the
    result. This is the `lsemRun` analogue of `lsemStraight_append`, specialised
    to the `comToBody`/`comToLfundefPhysAbi` shape `body ++ [Lret] ++ rest` — the
    decomposition the whole-function `toLprogPhysAbi_lsem_goal` peels by. -/
theorem lsemRun_body_ret {w : Nat} (body rest : List LinstrR) (s : Lstate w)
    (h : .Lret ∉ body) :
    lsemRun (body ++ .Lret :: rest) s = lsemStraight body s := by
  induction body generalizing s with
  | nil => simp
  | cons i is ih =>
      have hi : i ≠ .Lret := fun he => h (he ▸ List.mem_cons_self ..)
      have hmem : .Lret ∉ is := fun hm => h (List.mem_cons_of_mem _ hm)
      rw [List.cons_append, lsemRun_cons _ _ _ hi, lsemStraight_cons]
      cases lsemStep i s with
      | none => rfl
      | some s' => exact ih s' hmem

/-- `lsemRun` is deterministic (a function). -/
theorem lsemRun_deterministic {w : Nat} (is : List LinstrR) (s t1 t2 : Lstate w)
    (h1 : lsemRun is s = some t1) (h2 : lsemRun is s = some t2) : t1 = t2 := by
  rw [h1] at h2; exact Option.some.inj h2

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
