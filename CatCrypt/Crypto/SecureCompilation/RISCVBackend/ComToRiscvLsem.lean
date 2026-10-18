/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscv64Refinement
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RegToRiscv
public import CatCrypt.Crypto.SecureCompilation.MultiBackendDemo

/-!
# `Com → RISC-V`: a Sail-related block-execution model and value preservation

This module defines the target-model structure `MachineModel`, used by the
RISC-V and AArch64 backends. For the RV64 base-ALU fragment, it defines a
`MachineModel` whose `exec` is the `runRBlock64` block fold and relates each
base-ALU step of that fold to the `execute_RTYPE` clause of an in-file excerpt
of the sail-riscv-lean generated model (`SailRiscv64Refinement`).

## Dependencies

* **The block model** — `RiscvModel64.runRBlock64` (the `evalRInst64` fold) and
  `runRBlock64_append`.
* **The whole-`Com` value chain** — `MultiBackendDemo.com_riscv_e2e`: for a `Com`
  satisfying `ComOK` over an `AllReg64` context, run from a state whose registers
  are `envOf Γ.length V`, the RV64 machine run computes `Com.denote`. It composes
  `ScalarLinDeBruijn.comToReg_faithful` (the de-Bruijn front),
  `ScalarLin.compile_denote_pure_on` (the neutral backend lift), and
  `RegToRiscv.regToROp_denote` (the `ScalarTarget` theorem). Its machine
  semantics is the hand-written `evalRInst64`.
* **The per-op Sail refinement** — `SailRiscv64Ref.rtype_{add,sub,and,or,xor}`:
  for `rd` with `rd.toNat ≠ 0`, the value the in-file `execute_RTYPE` excerpt
  writes to `rd` equals the corresponding `RiscvModel64` op on the operands. The
  excerpt is a hand copy of the sail-riscv-lean generated output (commit
  `9eba3f07`); its fidelity to that output is not machine-checked in this
  repository.

## Main results

`MachineModel` is the target-model structure that `riscvBaseAluModel`,
`ComToRiscvMulLsem.riscvArithMulModel` and `ComToArmLsem.armBaseAluModel`
instantiate.

`com_riscv_e2e` is stated over the hand-written `evalRInst64`. The Sail excerpt
uses a different register representation (`RegFile = BitVec 5 → BitVec 64`, run
via `runRd`). This module relates the two for the five ops ADD/SUB/AND/OR/XOR:

1. **`riscvStep64_sail_grounded`** — for a base-ALU `RInst64` whose destination
   name is neither `"zero"` nor `"x0"`, under a register-name ↔ register-number
   alignment `RegAlign s rf nm` with `(nm rd).toNat ≠ 0`, the value `evalRInst64`
   writes to the destination equals the value the Sail `execute_RTYPE` excerpt
   writes (`runRd …`).
2. **`comToRiscvLsem_correct`** (main theorem) — for `ComBaseAlu com`,
   `AllReg64 Γ` and a start state with `s.regs = envOf Γ.length V`, the RV64
   `runRBlock64` execution of the compiled-and-lowered block, read at the result
   register, equals `Com.denote com V` (via `com_riscv_e2e`), and every
   instruction it runs is base-ALU (`riscvBlock_all_baseAlu`). The per-step Sail
   relation of item 1 applies to these instructions under its own hypotheses; it
   is not a conjunct of this theorem.
3. **`riscvBaseAluModel`** — a `MachineModel` with `exec := runRBlock64` and
   `validated := RiscvBaseAluGrounded` (the statement of item 1), proved by
   `riscvBaseAluGrounded_proof`.

## Scope: base-ALU only

Covered: **ADD, SUB, AND, OR, XOR**, the RV64I R-type ops for which
`SailRiscv64Ref` proves an `execute_RTYPE` refinement. `MUL`/`MULHU` are not
covered here: `SailRiscv64Ref.rtype_mul`/`rtype_mulhu` are proved against
`execute_MUL`, a different Sail clause, and are used in
`RISCVBackend/ComToRiscvMulLsem.lean`. `SLTU` (carry synthesis) is not in this
statement.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend.ComToRiscvLsem

open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RegToRiscv
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscv64Ref
open CatCrypt.Crypto.SecureCompilation.ScalarLin
open CatCrypt.Crypto.SecureCompilation.ScalarLinFront
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
open CatCrypt.Crypto.SecureCompilation.MultiBackendDemo
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 0. Target machine models -/

/-- **A target machine model.** For one target ISA: the emitted code type
    `Code`, the machine state `State`, the value carrier `Value` with the maps
    `encodeIn` and `decodeOut`, the execution semantics `exec`, and the
    proposition `validated` that the model's execution satisfies. -/
structure MachineModel where
  /-- The emitted artifact for this ISA (e.g. an ARM or RISC-V instruction
      list). -/
  Code : Type
  /-- The machine state the execution semantics acts on. -/
  State : Type
  /-- The abstract value the source program computes (the carrier `decodeOut`
      reads back to). -/
  Value : Type
  /-- Encode an input value into an initial machine state. -/
  encodeIn : Value → State
  /-- Decode an output value out of a final machine state. -/
  decodeOut : State → Value
  /-- The execution semantics: run the emitted code on a state. -/
  exec : Code → State → State
  /-- The proposition the model's execution is validated against, stated per
      instance. -/
  validated : Prop

/-! ## 1. The base-ALU fragment (the Sail-refined R-type subset) -/

/-- A base-ALU `RInst64`: the five RV64I R-type ops with an `execute_RTYPE` Sail
    refinement (ADD/SUB/AND/OR/XOR). `MUL`/`MULHU` (a different Sail clause),
    `SLTU`, the shifts, `LI`/`MV` are *not* base-ALU here. -/
def IsBaseAlu : RInst64 → Prop
  | .add .. | .sub .. | .and .. | .or .. | .xor .. => True
  | _ => False

/-- The Sail `rop` a base-ALU `RInst64` selects in `execute_RTYPE`. -/
def rinstRop : RInst64 → rop
  | .add .. => .ADD | .sub .. => .SUB | .and .. => .AND
  | .or  .. => .OR  | .xor .. => .XOR | _ => .ADD

/-- The destination register name of a base-ALU `RInst64`. -/
def rinstD : RInst64 → String
  | .add d _ _ | .sub d _ _ | .and d _ _ | .or d _ _ | .xor d _ _ => d | _ => ""

/-- The first source register name. -/
def rinstA : RInst64 → String
  | .add _ a _ | .sub _ a _ | .and _ a _ | .or _ a _ | .xor _ a _ => a | _ => ""

/-- The second source register name. -/
def rinstB : RInst64 → String
  | .add _ _ b | .sub _ _ b | .and _ _ b | .or _ _ b | .xor _ _ b => b | _ => ""

/-- **Register-name ↔ register-number alignment.** The model's string-keyed
    `RState64` and Sail's number-keyed `RegFile = BitVec 5 → BitVec 64` agree
    through the naming map `nm`: every name reads the same word in both. This is
    the (per-allocation) bridge the ABI register allocator must respect. -/
def RegAlign (s : RState64) (rf : RegFile) (nm : String → BitVec 5) : Prop :=
  ∀ r : String, rget rf (nm r) = s.get r

/-! ## 2. Per-op agreement with the Sail excerpt -/

/-- **Per-op agreement of `evalRInst64` with the Sail `execute_RTYPE` excerpt.**
    For a base-ALU `RInst64` whose destination name is neither `"zero"` nor
    `"x0"`, under a register-name alignment `RegAlign s rf nm` with
    `(nm (rinstD i)).toNat ≠ 0`, the value `evalRInst64` writes to the destination
    equals the value the in-file `execute_RTYPE` excerpt writes to `rd`
    (`runRd …`). Each arm applies the corresponding `SailRiscv64Ref.rtype_*`
    refinement; the non-base-ALU arms are excluded by `IsBaseAlu`. -/
theorem riscvStep64_sail_grounded
    (s : RState64) (rf : RegFile) (nm : String → BitVec 5) (i : RInst64)
    (hbase : IsBaseAlu i)
    (hdst : ¬ (rinstD i = "zero" ∨ rinstD i = "x0"))
    (halign : RegAlign s rf nm)
    (hrd : (nm (rinstD i)).toNat ≠ 0) :
    (evalRInst64 s i).get (rinstD i)
      = runRd (execute_RTYPE ⟨nm (rinstB i)⟩ ⟨nm (rinstA i)⟩ ⟨nm (rinstD i)⟩ (rinstRop i))
          rf (nm (rinstD i)) := by
  cases i with
  | add d a b =>
      simp only [rinstD, rinstA, rinstB, rinstRop] at *
      rw [rtype_add rf (nm a) (nm b) (nm d) hrd, halign a, halign b]
      simp only [evalRInst64, RState64.get_set_same _ _ _ hdst, opAdd64]
  | sub d a b =>
      simp only [rinstD, rinstA, rinstB, rinstRop] at *
      rw [rtype_sub rf (nm a) (nm b) (nm d) hrd, halign a, halign b]
      simp only [evalRInst64, RState64.get_set_same _ _ _ hdst, opSub64]
  | and d a b =>
      simp only [rinstD, rinstA, rinstB, rinstRop] at *
      rw [rtype_and rf (nm a) (nm b) (nm d) hrd, halign a, halign b]
      simp only [evalRInst64, RState64.get_set_same _ _ _ hdst, opAnd64]
  | or d a b =>
      simp only [rinstD, rinstA, rinstB, rinstRop] at *
      rw [rtype_or rf (nm a) (nm b) (nm d) hrd, halign a, halign b]
      simp only [evalRInst64, RState64.get_set_same _ _ _ hdst, opOr64]
  | xor d a b =>
      simp only [rinstD, rinstA, rinstB, rinstRop] at *
      rw [rtype_xor rf (nm a) (nm b) (nm d) hrd, halign a, halign b]
      simp only [evalRInst64, RState64.get_set_same _ _ _ hdst, opXor64]
  | sltu d a b => exact absurd hbase (by simp [IsBaseAlu])
  | mul d a b => exact absurd hbase (by simp [IsBaseAlu])
  | mulhu d a b => exact absurd hbase (by simp [IsBaseAlu])
  | li d imm => exact absurd hbase (by simp [IsBaseAlu])
  | mv d a => exact absurd hbase (by simp [IsBaseAlu])
  | srli d a sh => exact absurd hbase (by simp [IsBaseAlu])
  | slli d a sh => exact absurd hbase (by simp [IsBaseAlu])

/-! ## 3. The compiled block is entirely base-ALU

The lowered block of a base-ALU `Com` contains only base-ALU instructions, the
instructions to which `riscvStep64_sail_grounded` applies. -/

/-- A `RegStmt` whose RV64 selection + lowering is the base-ALU fragment: the five
    binary ALU ops the front emits for `regArith {add,sub,and,or,xor}`. -/
def RegBaseAlu : RegStmt → Prop
  | .add .. | .sub .. | .and .. | .orr .. | .eor .. => True
  | _ => False

/-- One base-ALU `RegStmt` lowers (`regStmtToROp` then `toRInst64`) to all
    base-ALU `RInst64`s. -/
theorem stmt_lower_base (stmt : RegStmt) (h : RegBaseAlu stmt) :
    ∀ i ∈ (regStmtToROp stmt).flatMap toRInst64, IsBaseAlu i := by
  cases stmt <;> simp_all [RegBaseAlu, regStmtToROp, toRInst64, IsBaseAlu]

/-- A whole base-ALU `RegProg` lowers to an all-base-ALU `RInst64` block. -/
theorem regprog_lower_base (p : RegProg) (hp : ∀ stmt ∈ p, RegBaseAlu stmt) :
    ∀ i ∈ lowerRBlock64 (regToROp p), IsBaseAlu i := by
  intro i hi
  rw [show lowerRBlock64 (regToROp p) = (p.flatMap regStmtToROp).flatMap toRInst64 from rfl,
      List.flatMap_assoc, List.mem_flatMap] at hi
  obtain ⟨stmt, hstmt, hi'⟩ := hi
  exact stmt_lower_base stmt (hp stmt hstmt) i hi'

/-! ### The `Com`-level base-ALU restriction -/

/-- A `JasminOp` in the base-ALU fragment: `regArith {add,sub,and,or,xor}` at
    width 64. -/
def BaseAluOp (op : JasminOp) : Prop :=
  ∃ bop, op = JasminOp.regArith bop 64 ∧
    (bop = .add ∨ bop = .sub ∨ bop = .and ∨ bop = .or ∨ bop = .xor)

/-- A base-ALU op is a `SupportedOp` (so `com_riscv_e2e` applies to a base-ALU
    `Com`). -/
theorem BaseAluOp.toSupported {op : JasminOp} (h : BaseAluOp op) : SupportedOp op := by
  obtain ⟨bop, rfl, hbop⟩ := h
  exact Or.inl ⟨bop, rfl, by rcases hbop with h|h|h|h|h <;> subst h <;> simp⟩

/-- The base-ALU op selects exactly one base-ALU `RegStmt`. -/
theorem opToStmts_base (d : String) (srcs : List String) (op : JasminOp)
    (hop : BaseAluOp op) : ∀ stmt ∈ opToStmts d srcs op, RegBaseAlu stmt := by
  obtain ⟨bop, rfl, hbop⟩ := hop
  rcases hbop with h|h|h|h|h <;> subst h <;>
    (rcases srcs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp_all [opToStmts, RegBaseAlu])

/-- The straight-line `Com` fragment whose every op is base-ALU (a sub-fragment of
    `ScalarLinDeBruijn.ComOK`). -/
inductive ComBaseAlu : {Γ : Ctxt jasminDialect} → Com jasminDialect Γ (.reg 64) → Prop where
  /-- A `.ret` is base-ALU. -/
  | ret {Γ : Ctxt jasminDialect} (v : Ctxt.Var Γ (.reg 64)) : ComBaseAlu (.ret v)
  /-- A `.var` whose op is base-ALU, over a base-ALU body. -/
  | var {Γ : Ctxt jasminDialect} {e : Expr jasminDialect Γ (.reg 64)}
      {body : Com jasminDialect ((.reg 64) :: Γ) (.reg 64)}
      (hb : BaseAluOp e.op) (hbody : ComBaseAlu body) : ComBaseAlu (.var e body)

/-- A base-ALU `Com` is a supported `Com` (the hypothesis `com_riscv_e2e` needs). -/
theorem ComBaseAlu.toComOK : ∀ {Γ : Ctxt jasminDialect} {com : Com jasminDialect Γ (.reg 64)},
    ComBaseAlu com → ComOK com := by
  intro Γ com h
  induction h with
  | ret v => exact ComOK.ret v
  | var hb hbody ih => exact ComOK.var hb.toSupported ih

/-- **Every statement the front emits from a base-ALU `Com` is `RegBaseAlu`.** -/
theorem comToRegProg_RegBaseAlu :
    ∀ {Γ : Ctxt jasminDialect} {com : Com jasminDialect Γ (.reg 64)},
      ComBaseAlu com → ∀ (depth : Nat), ∀ stmt ∈ comToRegProg com depth, RegBaseAlu stmt := by
  intro Γ com h
  induction h with
  | ret v =>
      intro depth stmt hstmt
      simp only [comToRegProg_ret] at hstmt
      exact absurd hstmt List.not_mem_nil
  | @var Γ e body hb hbody ih =>
      intro depth stmt hstmt
      rw [comToRegProg_var] at hstmt
      rcases List.mem_append.mp hstmt with hh | hh
      · exact opToStmts_base _ _ _ hb stmt hh
      · exact ih (depth + 1) stmt hh

/-- **The compiled-and-lowered RV64 block of a base-ALU `Com` is all base-ALU.**
    Every instruction the model executes is therefore in the domain of
    `riscvStep64_sail_grounded`, which relates it to the Sail excerpt under that
    theorem's register hypotheses. -/
theorem riscvBlock_all_baseAlu {Γ : Ctxt jasminDialect}
    {com : Com jasminDialect Γ (.reg 64)} (hba : ComBaseAlu com) :
    ∀ i ∈ lowerRBlock64 (regToROp (comToRegProg com Γ.length)), IsBaseAlu i :=
  regprog_lower_base (comToRegProg com Γ.length) (comToRegProg_RegBaseAlu hba Γ.length)

/-! ## 4. `Com → RISC-V` value preservation -/

/-- **Whole-`Com` value preservation for RV64.** For a `Com` with
    `ComBaseAlu com` over a context with `AllReg64 Γ`, and a start state `s` with
    `s.regs = envOf Γ.length V`, executing the compiled-and-lowered RV64 block
    with `runRBlock64`:

    1. yields a state whose register `comRetName com Γ.length` holds
       `Com.denote com V` (via `com_riscv_e2e`, which composes
       `comToReg_faithful`, `compile_denote_pure_on` and `regToROp_denote`), and
    2. executes only base-ALU instructions (`riscvBlock_all_baseAlu`).

    Conjunct (2) states membership only. For each such instruction,
    `riscvStep64_sail_grounded` relates its `evalRInst64` step to the
    `execute_RTYPE` excerpt under a register alignment, a destination other than
    `"zero"`/`"x0"`, and a nonzero Sail register number; those hypotheses are not
    discharged here. The execution semantics is `runRBlock64`. -/
theorem comToRiscvLsem_correct {Γ : Ctxt jasminDialect}
    {com : Com jasminDialect Γ (.reg 64)} (hba : ComBaseAlu com) (hΓ : AllReg64 Γ)
    (V : Ctxt.Valuation Γ) (s : RState64) (hs : s.regs = envOf Γ.length V) :
    (runRBlock64 s (lowerRBlock64 (regToROp (comToRegProg com Γ.length)))).regs
        (comRetName com Γ.length)
      = Com.denote com V
    ∧ (∀ i ∈ lowerRBlock64 (regToROp (comToRegProg com Γ.length)), IsBaseAlu i) :=
  ⟨com_riscv_e2e hba.toComOK hΓ V s hs, riscvBlock_all_baseAlu hba⟩

/-! ## 5. A RISC-V `MachineModel` with `exec := runRBlock64` -/

/-- The statement of `riscvStep64_sail_grounded` as a proposition, used as the
    `MachineModel.validated` field. It is value-level: for
    every base-ALU `RInst64` with destination other than `"zero"`/`"x0"`, under
    `RegAlign s rf nm` and `(nm (rinstD i)).toNat ≠ 0`, the value `evalRInst64`
    writes to the destination equals the value the `execute_RTYPE` excerpt
    writes. -/
def RiscvBaseAluGrounded : Prop :=
  ∀ (s : RState64) (rf : RegFile) (nm : String → BitVec 5) (i : RInst64),
    IsBaseAlu i → ¬ (rinstD i = "zero" ∨ rinstD i = "x0") → RegAlign s rf nm →
    (nm (rinstD i)).toNat ≠ 0 →
    (evalRInst64 s i).get (rinstD i)
      = runRd (execute_RTYPE ⟨nm (rinstB i)⟩ ⟨nm (rinstA i)⟩ ⟨nm (rinstD i)⟩ (rinstRop i))
          rf (nm (rinstD i))

/-- `RiscvBaseAluGrounded` holds, by `riscvStep64_sail_grounded`. -/
theorem riscvBaseAluGrounded_proof : RiscvBaseAluGrounded :=
  fun s rf nm i hbase hdst halign hrd => riscvStep64_sail_grounded s rf nm i hbase hdst halign hrd

/-- **The RISC-V base-ALU `MachineModel`.** Its `exec` is the `runRBlock64` block
    fold over `RState64`, and its `validated` field is `RiscvBaseAluGrounded`
    (proved by `riscvBaseAluGrounded_proof`). `Code` is the executed `RInst64`
    list; `State` and `Value` are `RState64`; `encodeIn` and `decodeOut` are `id`. -/
def riscvBaseAluModel : MachineModel where
  Code := List RInst64
  State := RState64
  Value := RState64
  encodeIn := id
  decodeOut := id
  exec := fun code s => runRBlock64 s code
  validated := RiscvBaseAluGrounded

/-- The model's `exec` is the `runRBlock64` block fold. -/
theorem riscvBaseAluModel_exec (code : List RInst64) (s : RState64) :
    riscvBaseAluModel.exec code s = runRBlock64 s code := rfl

/-- The model's `validated` field, `RiscvBaseAluGrounded`, holds by
    `riscvBaseAluGrounded_proof`. -/
theorem riscvBaseAluModel_validated : riscvBaseAluModel.validated :=
  riscvBaseAluGrounded_proof

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.ComToRiscvLsem
