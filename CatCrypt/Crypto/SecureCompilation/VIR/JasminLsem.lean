/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module
import all CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-!
# A faithful Lean model of jasmin's linear semantics `lsem` — increment 1

This module is **increment 1** of porting jasmin's `proofs/lang/linear_sem.v`
(`lsem`/`lsem1`/`eval_instr`) to Lean. It provides the *semantics-foundation*
half of the Com→`lsem` faithfulness predicate `ComLsemExportFaithful`
(`LsemPortAll`): the Lean model of jasmin's `lsem` over which that predicate is
stated and proved. This file provides that model **for the straight-line
fragment**.

## Scope of increment 1

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
  read off. The single-step `lsemStep .Lret` stays `none` (it is control
  flow at the instruction level); the terminator semantics live in the
  whole-function fold `lsemRun`, which agrees with `lsemStraight` on the
  `Lret`-free body prefix (`lsemRun_eq_lsemStraight` / `lsemRun_body_ret`).

**Out of scope for increment 1** (control flow / effects — modeled as `none`):
`Lgoto`, `Lcond`, `Ligoto`, `Lcall`, `LstoreLabel`, `Lsyscall`.
Each of these in Coq calls `eval_jump`/`find_label`/`rencode_label`/
`exec_syscall`, i.e. it reads the whole-program label table `label_in_lprog` or
the syscall oracle. Modeling them faithfully needs the program `P`, the label
machinery (`find_label`, `eval_jump`), and the memory/syscall effects — that is
**increment 2/3**. Here their `lsemStep` is `none` (not modeled in
the straight-line foundation).

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

@[expose] public section

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

@[simp] theorem Lstate.lmem_nextPc {w : Nat} (s : Lstate w) : s.nextPc.lmem = s.lmem := rfl

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
    `JasminLprogExport.binOpName` (binary register arithmetic), the immediate
    `MOV` (a `regConst`/`castW` nullary/unary move), the ABI `MOVQ` (the 64-bit
    register/memory move the prologue/arg-materialization/epilogue emit; same word
    semantics as `MOV`), and the widening-multiply / carry-chain word ops
    `MULXHI`/`ADCX`/`ADCXHI` (the high-word `MULX` binding and the carry-chain
    add's data and carry-out bindings), denoted by the same `JasminDialect`
    functions `mulHiW`/`addCarryWord`/`carryOutBit` the dialect uses for
    `mulhi`/`addCarryLo`/`addCarryHi`, and the conditional move `CMOV` (the
    image of the dialect's `select`), denoted by the dialect's `selectW`.

    Returns `none` for any opcode outside the modeled straight-line word
    fragment (e.g. `CALL:…`, `LOAD`/`STORE`) — partiality, not a
    default value. -/
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
  -- `SET<cc>`: the materialised comparison, the image of the dialect's `cmp` and
  -- `cmpImm` under `opToLinstrR`. The result is the dialect's `cmpBit` at the
  -- uniform width, so the destination holds `1` when the relation holds and `0`
  -- otherwise.
  | "SETE", [a, b] => some (BitVec.setWidth w (cmpBit .eq a b))
  | "SETNE", [a, b] => some (BitVec.setWidth w (cmpBit .ne a b))
  | "SETB", [a, b] => some (BitVec.setWidth w (cmpBit .ult a b))
  | "SETBE", [a, b] => some (BitVec.setWidth w (cmpBit .ule a b))
  | "SETA", [a, b] => some (BitVec.setWidth w (cmpBit .ugt a b))
  | "SETAE", [a, b] => some (BitVec.setWidth w (cmpBit .uge a b))
  | "MOV", [a] => some a
  -- `MULXHI`: the high word of the full product `a * b` (the `hi` binding of a
  -- `MULX`; the low word is exported as `MUL`, already modeled). Denoted by the
  -- dialect's `mulHiW`, so the `lsem` model and the `mulhi` dialect op agree.
  | "MULXHI", [a, b] => some (mulHiW a b)
  -- `ADCX`: the data word of one carry-chain add `a + b + carry-in`. The carry-in
  -- register holds a `0`/`1` value at the uniform width; its low bit
  -- (`BitVec.setWidth 1`) is the `reg 1` carry the dialect threads. Denoted by
  -- the dialect's `addCarryWord`.
  | "ADCX", [a, b, cin] => some (addCarryWord a b (BitVec.setWidth 1 cin))
  -- `ADCXHI`: the carry-out bit of that same add, packaged at the uniform width
  -- (`BitVec.setWidth w` of the dialect's `carryOutBit`), so it threads into the
  -- next limb's carry-in register.
  | "ADCXHI", [a, b, cin] => some (BitVec.setWidth w (carryOutBit a b (BitVec.setWidth 1 cin)))
  -- `CMOV`: the conditional move, the image of the dialect's `select w` under
  -- `opToLinstrR`, with the operands in the dialect's source order
  -- `[cond, a, b]` — the condition first, then the two data words. The condition
  -- register holds a `0`/`1` value at the uniform width and its low bit
  -- (`BitVec.setWidth 1`) is the `reg 1` condition the dialect threads, as for
  -- the carry-in of `ADCX`. The result is the dialect's `selectW` of that bit:
  -- the first data word `a` when the bit is one, the second data word `b` when
  -- it is zero. The machine instruction is an x86 `cmov<cc>` at the width the
  -- mnemonic's tag carries, taken when the condition word is non-zero; both data
  -- words are read, so there is no condition-dependent branch.
  | "CMOV", [c, a, b] => some (selectW (BitVec.setWidth 1 c) a b)
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
  -- `MOV:8` / `MOV:16`: the narrow ABI buffer moves the exporter tags at a `u8` /
  -- `u16` C-buffer element width (`abiMovBuf`). The asm printer renders a
  -- memory-source narrow move as the zero-extending `movzbl` / `movzwl` load and a
  -- memory-destination one as the width-exact `movb` / `movw` store. Both directions
  -- have the same word semantics at this model's granularity: keep the low `8` /
  -- `16` bits of the single evaluated source, clearing the rest (`BitVec.zeroExtend`
  -- of the narrow slice), which is exactly `movz{b,w}l`'s zero-extend on a load and
  -- the low-bits value a byte / word store deposits. `stripWidthTag` peels only the
  -- `:64` tag, so the `:8` / `:16` tag survives to this arm.
  | "MOV:8", [a] => some (a &&& BitVec.ofNat w 0xFF)
  | "MOV:16", [a] => some (a &&& BitVec.ofNat w 0xFFFF)
  -- Runtime-indexed memory opcodes are modeled by `lsemStep`'s `.arrIdx` arm, not
  -- by `applyOpn`. They are named here, before the count-tagged shift arm, so that
  -- `applyOpn "LOADIDX"`/`"STOREIDX"` still reduces to `none` on a symbolic source
  -- list — the shift arm below matches any single-source op and would otherwise
  -- block that reduction on the list shape.
  | "LOADIDX", _ => none
  | "STOREIDX", _ => none
  -- Count-tagged immediate shift / rotate (`SHL:0`, `SHR:32`, `SAR:k`, `ROL:k`,
  -- `ROR:k`): a single-source op whose mnemonic carries the shift count.
  -- `stripWidthTag` keeps the count tag, so the mnemonic reaching `applyOpn` still
  -- carries it and `parseImmShiftMnem` recovers the direction and count. The result
  -- is that shift / rotate applied to the one evaluated source word. Distinct from
  -- the two-source `SHL`/`SHR` arms above, which are the variable-count form (count
  -- in a register/immediate operand); this arm requires exactly one source.
  | opn, [a] =>
      match parseImmShiftMnem opn with
      | some (att, k, _) =>
          some (if att = "shl" then a <<< k
                else if att = "sar" then BitVec.sshiftRight a k
                else if att = "rol" then a.rotateLeft k
                else if att = "ror" then a.rotateRight k
                else a >>> k)
      | none => none
  | _, _ => none

/-- `applyOpn` agrees with `JasminBinOp.apply` (the dialect denotation) on the
    binary register-arithmetic opcodes that `binOpName` produces. This is the
    fidelity tie between the `lsem` word-op model and the dialect semantics that
    `Com.toLprog` lowers from. -/
theorem applyOpn_binOpName {w : Nat} (bop : JasminBinOp) (a b : BitVec w) :
    applyOpn (binOpName bop) [a, b] = some (bop.apply a b) := by
  cases bop <;> rfl

/-- `applyOpn` on `MULXHI` denotes the dialect's `mulHiW` — the fidelity tie
    between the `lsem` high-multiply model and the `mulhi` dialect op. -/
@[simp] theorem applyOpn_mulhi {w : Nat} (a b : BitVec w) :
    applyOpn "MULXHI" [a, b] = some (mulHiW a b) := rfl

/-- `applyOpn` on `ADCX` denotes the dialect's `addCarryWord`, reading the
    carry-in register's low bit — the fidelity tie for the carry-chain data word
    (`addCarryLo`). -/
@[simp] theorem applyOpn_addCarryLo {w : Nat} (a b cin : BitVec w) :
    applyOpn "ADCX" [a, b, cin] = some (addCarryWord a b (BitVec.setWidth 1 cin)) := rfl

/-- `applyOpn` on `ADCXHI` denotes the dialect's `carryOutBit`, widened to the
    uniform word width — the fidelity tie for the carry-out bit (`addCarryHi`). -/
@[simp] theorem applyOpn_addCarryHi {w : Nat} (a b cin : BitVec w) :
    applyOpn "ADCXHI" [a, b, cin]
      = some (BitVec.setWidth w (carryOutBit a b (BitVec.setWidth 1 cin))) := rfl

/-- `applyOpn` on `CMOV` denotes the dialect's `selectW`, reading the condition
    register's low bit — the fidelity tie for the conditional move (`select`).
    The operand order is the dialect's: condition, then the word taken when the
    condition bit is one, then the word taken when it is zero. -/
@[simp] theorem applyOpn_select {w : Nat} (c a b : BitVec w) :
    applyOpn "CMOV" [c, a, b] = some (selectW (BitVec.setWidth 1 c) a b) := rfl

/-- `applyOpn` on the `SET<cc>` mnemonic of a condition code denotes the dialect's
    `cmpBit`, widened to the uniform word width: the fidelity tie for the
    comparison ops `cmp` and `cmpImm`. -/
@[simp] theorem applyOpn_cmp {w : Nat} (c : JasminCmp) (a b : BitVec w) :
    applyOpn (cmpName c) [a, b] = some (BitVec.setWidth w (cmpBit c a b)) := by
  cases c <;> rfl

/-- A materialised comparison result is `0` or `1`. -/
theorem setWidth_cmpBit_lt_two {w v : Nat} (c : JasminCmp) (a b : BitVec v) :
    (BitVec.setWidth w (cmpBit c a b)).toNat < 2 := by
  have h := (cmpBit c a b).isLt
  have := BitVec.toNat_setWidth w (cmpBit c a b)
  rw [this]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by simpa using h)

/-- Reading the low bit of a materialised comparison result recovers the
    comparison bit, for every positive word width. -/
theorem setWidth_one_setWidth_cmpBit {w v : Nat} (hw : 0 < w) (c : JasminCmp)
    (a b : BitVec v) :
    BitVec.setWidth 1 (BitVec.setWidth w (cmpBit c a b)) = cmpBit c a b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have h := (cmpBit c a b).isLt
  have h2 : 2 ≤ 2 ^ w := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hw
  have h3 : (cmpBit c a b).toNat % 2 ^ w = (cmpBit c a b).toNat :=
    Nat.mod_eq_of_lt (by omega)
  rw [h3]
  exact Nat.mod_eq_of_lt (by omega)

/-- The ABI `MOVQ` opcode copies its single source word unchanged — the fidelity
    tie for the 64-bit move the prologue/arg-materialization/epilogue emit (same
    word semantics as `MOV`). -/
@[simp] theorem applyOpn_MOVQ {w : Nat} (a : BitVec w) :
    applyOpn "MOVQ" [a] = some a := rfl

/-- `MOVQ` carries no `":64"` width tag, so `stripWidthTag` leaves it unchanged —
    the body mnemonic the `lsemStep` `Lopn` arm recovers it as. -/
@[simp] theorem stripWidthTag_MOVQ : stripWidthTag "MOVQ" = "MOVQ" := by decide +kernel

/-- `MOVQ` and `MOV` denote the same word op (a pure copy). -/
theorem applyOpn_MOVQ_eq_MOV {w : Nat} (a : BitVec w) :
    applyOpn "MOVQ" [a] = applyOpn "MOV" [a] := rfl

/-- The narrow `MOV:8` buffer move keeps the low byte of its source (the
    zero-extend a `movzbl` load and the low-bits value a `movb` store share). -/
@[simp] theorem applyOpn_MOV8 {w : Nat} (a : BitVec w) :
    applyOpn "MOV:8" [a] = some (a &&& BitVec.ofNat w 0xFF) := rfl

/-- The narrow `MOV:16` buffer move keeps the low word of its source (the
    zero-extend a `movzwl` load and the low-bits value a `movw` store share). -/
@[simp] theorem applyOpn_MOV16 {w : Nat} (a : BitVec w) :
    applyOpn "MOV:16" [a] = some (a &&& BitVec.ofNat w 0xFFFF) := rfl

/-! ## 3. `lsemStep` / `lsem1`: the single-instruction step

Mirror of Coq `eval_instr (i : linstr) (s1 : lstate) : exec lstate`
(`linear_sem.v` l.112–173), restricted to the straight-line cases. Coq's `exec`
monad is `result error`; we use `Option` (the partiality), with `none` for both
a type error (a modeled op applied to ill-typed args) and an out-of-scope
control-flow case. The distinction is documented per-arm. -/

/-- The single-step linear semantics for one `LinstrR`, faithful to Coq
    `eval_instr` on the straight-line cases:

    * `Lopn [dst] opn (.arrIdx base idx scale :: rest)` — a runtime-indexed
      memory op, recognised by its `.arrIdx`-headed source (the SIB cell
      `base[idx*scale]` at byte offset `scale · ⟦idx⟧`, the shape
      `JasminLprogExport` emits for `stackLoad`/`stackStore` with a register
      index). `LOADIDX` reads that cell into `dst` and bumps the pc; `STOREIDX`
      writes the trailing value operand into the cell, writes no register (the
      `.reg dst` is the dialect's nominal array-result name), and bumps the pc.
      An `.arrIdx`-headed source under any other opcode is unmodeled (`none`).
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
  | .Lopn [.reg dst] opn (.arrIdx base idx scale :: rest) =>
      let off : Int := Int.ofNat (scale * (s.lvm idx).toNat)
      if opn = "LOADIDX" then
        some ((s.setReg dst (s.lmem base off)).nextPc)
      else if opn = "STOREIDX" then
        match rest with
        | [val] =>
            some ({ s with lmem := fun b o =>
                      if b = base then (if o = off then evalOperand s val else s.lmem b o)
                      else s.lmem b o }.nextPc)
        | _ => none
      else
        -- Any other opcode over an `.arrIdx`-headed source falls through to the
        -- word-op path, byte-identical to the register arm below: the only
        -- additional behaviour of this arm is intercepting the two runtime-indexed
        -- memory opcodes, so every other modeled op keeps its meaning.
        match applyOpn (stripWidthTag opn)
            ((LOperand.arrIdx base idx scale :: rest).map (evalOperand s)) with
        | some v => some ((s.setReg dst v).nextPc)
        | none => none
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

/-! ### 3a. The step of the comparison heads

`opToLinstrR` emits `cmp c wOp` as `SET<cc>[:64] dst, a, b` and `cmpImm c wOp n`
as `SET<cc>[:64] dst, a, #n`; `applyOpn` models the mnemonic as the dialect's
`cmpBit`. -/

/-- `stripWidthTag` recovers the comparison mnemonic from its width-tagged form. -/
theorem stripWidthTag_withWidthTag_cmpName (wOp : Nat) (c : JasminCmp) :
    stripWidthTag (withWidthTag wOp (cmpName c)) = cmpName c := by
  unfold withWidthTag
  split <;> cases c <;> decide +kernel

/-- The exported `cmp` head writes the dialect's `cmpBit` of the two operand
    registers, widened to the word width, and advances the pc. -/
theorem lsemStep_cmp {w : Nat} (c : JasminCmp) (wOp : Nat) (nD nA nB : String)
    (s : Lstate w) :
    lsemStep (opToLinstrR (.cmp c wOp) nD [.reg nA, .reg nB]) s
      = some ((s.setReg nD
          (BitVec.setWidth w (cmpBit c (s.lvm nA) (s.lvm nB)))).nextPc) := by
  simp only [opToLinstrR, lsemStep, List.map_cons, List.map_nil, evalOperand,
    stripWidthTag_withWidthTag_cmpName, applyOpn_cmp]

/-- The exported `cmpImm` head writes the dialect's `cmpBit` of the operand
    register and the immediate, widened to the word width, and advances the pc. -/
theorem lsemStep_cmpImm {w : Nat} (c : JasminCmp) (wOp n : Nat) (nD nA : String)
    (s : Lstate w) :
    lsemStep (opToLinstrR (.cmpImm c wOp n) nD [.reg nA]) s
      = some ((s.setReg nD
          (BitVec.setWidth w (cmpBit c (s.lvm nA) (BitVec.ofNat w n)))).nextPc) := by
  simp only [opToLinstrR, List.cons_append, List.nil_append, lsemStep, List.map_cons,
    List.map_nil, evalOperand, stripWidthTag_withWidthTag_cmpName, applyOpn_cmp]

/-! ### 3a′. Reducing `lsemStep` past the `.arrIdx`-headed memory arm

The `lsemStep` `Lopn` cases are ordered so a runtime-indexed memory op
(`.arrIdx`-headed source) is intercepted before the register/word-op arm. A
proof reducing `lsemStep (.Lopn [.reg dst] opn srcs)` over a symbolic `srcs`
cannot decide which arm fires unless it knows the head is not `.arrIdx`. The two
lemmas here supply that: `resolveVar` never produces an `.arrIdx`, and given any
non-`.arrIdx`-headed `srcs` the step collapses to the word-op form. -/

/-- `resolveVar` returns either a register or an immediate, never a
    register-indexed (`.arrIdx`) operand. -/
theorem resolveVar_ne_arrIdx {Γ : Ctxt jasminDialect} {τ : JasminTy}
    (curDepth nArgs : Nat) (argNames : Nat → String) (immSlotMap : ImmSlotMap)
    (v : Ctxt.Var Γ τ) (base idx : String) (scale : Nat) :
    resolveVar curDepth nArgs argNames immSlotMap v ≠ LOperand.arrIdx base idx scale := by
  rw [resolveVar]
  split
  · split <;> simp
  · simp

/-- Reducer for a non-`.arrIdx`-headed source list: `lsemStep` of
    `Lopn [.reg dst] opn srcs` collapses to the word-op arm (`applyOpn` on the
    evaluated sources, write `dst`, bump the pc) whenever `srcs` does not start
    with an `.arrIdx` operand. The hypothesis is discharged by
    `resolveVar_ne_arrIdx` at the call sites where `srcs` is built from
    `resolveVar`. -/
theorem lsemStep_reg_srcs {w : Nat} (dst : String) (opn : String)
    (srcs : List LOperand) (s : Lstate w)
    (h : ∀ base idx scale rest, srcs ≠ LOperand.arrIdx base idx scale :: rest) :
    lsemStep (.Lopn [.reg dst] opn srcs) s
      = match applyOpn (stripWidthTag opn) (srcs.map (evalOperand s)) with
        | some v => some ((s.setReg dst v).nextPc)
        | none => none := by
  cases srcs with
  | nil => simp [lsemStep]
  | cons o rest =>
    cases o with
    | reg => simp [lsemStep]
    | arr => simp [lsemStep]
    | imm => simp [lsemStep]
    | arrIdx base idx scale => exact absurd rfl (h base idx scale rest)

/-- The two-source specialisation of `lsemStep_reg_srcs`: neither operand is an
    `.arrIdx`, so the step is the word-op arm on `[o0, o1]`. The common shape for
    binary-arithmetic call sites (`[resolveVar … a0, resolveVar … a1]`). -/
theorem lsemStep_reg_cons2 {w : Nat} (dst : String) (opn : String)
    (o0 o1 : LOperand) (s : Lstate w)
    (h0 : ∀ base idx scale, o0 ≠ LOperand.arrIdx base idx scale) :
    lsemStep (.Lopn [.reg dst] opn [o0, o1]) s
      = match applyOpn (stripWidthTag opn) [evalOperand s o0, evalOperand s o1] with
        | some v => some ((s.setReg dst v).nextPc)
        | none => none := by
  apply lsemStep_reg_srcs
  intro base idx scale rest hcontra
  exact h0 base idx scale (by cases hcontra; rfl)

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
  cases src <;> simp [lsemStep, applyOpn]

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

/-! ### 3b. Runtime-indexed memory step lemmas (`LOADIDX` / `STOREIDX`)

`JasminLprogExport` emits a register-indexed `stackLoad`/`stackStore` as an
`Lopn` whose first (and only address-carrying) source is the SIB operand
`.arrIdx base idx scale`. `lsemStep` recognises those two opcodes by that
`.arrIdx`-headed source: `LOADIDX` reads the addressed cell into the
destination register, `STOREIDX` writes the trailing value operand into the
cell. Both address the byte offset `scale · ⟦idx⟧` — the same effective offset
`evalOperand` reads an `.arrIdx` source at, so a `LOADIDX` after a `STOREIDX`
to the same `(base, idx, scale)` observes the stored word. -/

/-- **`LOADIDX` step.** Running `Lopn [.reg dst] "LOADIDX" [.arrIdx base idx scale]`
    reads the SIB cell `base[idx*scale]` (byte offset `scale · ⟦idx⟧`) into `dst`
    and advances the pc. The read value is exactly `evalOperand` on the same
    `.arrIdx` source. -/
theorem lsemStep_loadidx {w : Nat} (dst base idx : String) (scale : Nat)
    (s : Lstate w) :
    lsemStep (.Lopn [.reg dst] "LOADIDX" [.arrIdx base idx scale]) s
      = some ((s.setReg dst (evalOperand s (.arrIdx base idx scale))).nextPc) := by
  simp [lsemStep, evalOperand]

/-- **`STOREIDX` step.** Running
    `Lopn [.reg dst] "STOREIDX" [.arrIdx base idx scale, val]` writes
    `evalOperand s val` into the SIB cell `base[idx*scale]` (byte offset
    `scale · ⟦idx⟧`), leaves every register (and every other memory cell)
    unchanged, and advances the pc. The nominal destination register `dst` (the
    dialect's array-result name) is not written — a `STOREIDX` is a pure memory
    write. The `lmem` update coincides with `Lstate.setMem base (scale · ⟦idx⟧)`. -/
theorem lsemStep_storeidx {w : Nat} (dst base idx : String) (scale : Nat)
    (val : LOperand) (s : Lstate w) :
    lsemStep (.Lopn [.reg dst] "STOREIDX" [.arrIdx base idx scale, val]) s
      = some ({ s with lmem := fun b o =>
                  if b = base then
                    (if o = Int.ofNat (scale * (s.lvm idx).toNat) then evalOperand s val
                     else s.lmem b o)
                  else s.lmem b o }.nextPc) := by
  simp [lsemStep]

/-- The `STOREIDX` step writes the stored word into the addressed cell: reading
    `(base, scale · ⟦idx⟧)` from the resulting `lmem` returns `evalOperand s val`.
    The faithfulness fact that memory records the store. -/
theorem lsemStep_storeidx_lmem_hit {w : Nat} (dst base idx : String) (scale : Nat)
    (val : LOperand) (s t : Lstate w)
    (h : lsemStep (.Lopn [.reg dst] "STOREIDX" [.arrIdx base idx scale, val]) s = some t) :
    t.lmem base (Int.ofNat (scale * (s.lvm idx).toNat)) = evalOperand s val := by
  rw [lsemStep_storeidx] at h
  simp only [Option.some.injEq] at h
  subst h
  simp

/-- The `STOREIDX` step leaves the register file untouched: the resulting `lvm`
    equals `s.lvm` (the nominal destination register is not written). -/
theorem lsemStep_storeidx_lvm {w : Nat} (dst base idx : String) (scale : Nat)
    (val : LOperand) (s t : Lstate w)
    (h : lsemStep (.Lopn [.reg dst] "STOREIDX" [.arrIdx base idx scale, val]) s = some t) :
    t.lvm = s.lvm := by
  rw [lsemStep_storeidx] at h
  simp only [Option.some.injEq] at h
  subst h; rfl

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

/-- `stripWidthTag` fixes the carry-chain mnemonics — they carry no `":64"` tag,
    so the body mnemonic the `lsemStep` `Lopn` arm recovers them as. -/
@[simp] theorem stripWidthTag_MULXHI : stripWidthTag "MULXHI" = "MULXHI" := by decide +kernel

@[simp] theorem stripWidthTag_ADCX : stripWidthTag "ADCX" = "ADCX" := by decide +kernel

@[simp] theorem stripWidthTag_ADCXHI : stripWidthTag "ADCXHI" = "ADCXHI" := by decide +kernel

/-- **Non-vacuity witness.** A body holding the widening-multiply / carry-chain
    ops `MULXHI`/`ADCX`/`ADCXHI` runs to a defined state — `lsemStraight` is
    `some`, not `none`. Before these `applyOpn` arms, such a body short-circuited
    to `none` at the first `MULXHI`, making any store-preservation guarantee over
    an mpn/Montgomery carry body vacuous. -/
theorem lsemStraight_carryChain_isSome {w : Nat} (s : Lstate w) :
    (lsemStraight
      [ .Lopn [.reg "hi"] "MULXHI" [.reg "a", .reg "b"],
        .Lopn [.reg "d"] "ADCX" [.reg "a", .reg "b", .reg "c"],
        .Lopn [.reg "co"] "ADCXHI" [.reg "a", .reg "b", .reg "c"] ] s).isSome := by
  simp [lsemStraight, lsemStep, evalOperand]

/-! ## 5. The proved structural law: sequential composition (`lsem_trans`)

The straight-line analogue of Coq `lsem_trans` (`linear_sem.v` l.212–214,
transitivity of `clos_refl_trans`): running `xs ++ ys` is running `xs` then
running `ys` from the resulting state. Stated in `Option`-Kleisli form so it
holds unconditionally (both the success and the short-circuit-to-`none` cases).
This is the law a `Com.toLprog` simulation peels by (one binding at a time). -/

/-- **Sequential composition** of straight-line execution: `lsemStraight` of a
    concatenation is the Kleisli composite of the two halves. The increment-1
    characterising law (faithful straight-line restriction of `lsem_trans`).
    Fully proved, proved by induction on the prefix. -/
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
