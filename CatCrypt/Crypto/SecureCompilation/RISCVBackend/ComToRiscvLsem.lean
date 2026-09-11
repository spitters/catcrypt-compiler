/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscv64Refinement
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RegToRiscv
public import CatCrypt.Crypto.SecureCompilation.MultiBackendDemo
public import CatCrypt.Crypto.SecureCompilation.VIR.Compiler

/-!
# `Com → RISC-V`: a Sail-grounded block-execution model + value-preservation keystone

This module turns the RISC-V path into a **genuine functional semantics** for the
RV64 base-ALU fragment that already carries a Sail refinement, replacing the
`MachineModel.exec := id` validation shell of `VIR/Compiler.lean`'s `latticeModel`
(`exec := fun _ s => s`) with a `MachineModel` whose `exec` is the real
`runRBlock64` block fold, *grounded* in the per-op `riscv/sail-riscv`-validated
semantics.

## What was already in the tree (reused verbatim, not re-derived)

* **The block model** — `RiscvModel64.runRBlock64` (the `evalRInst64` fold) and
  `runRBlock64_append`, already proved.
* **The whole-`Com` value chain** — `MultiBackendDemo.com_riscv_e2e`: for a
  supported all-`reg 64` `Com`, the RV64 machine run computes `Com.denote`. This
  chains `ScalarLinDeBruijn.comToReg_faithful` (the de-Bruijn front),
  `ScalarLin.compile_denote_pure_on` (the neutral backend lift), and
  `RegToRiscv.regToROp_denote` (the `ScalarTarget` keystone). The chain terminates
  at the model `evalRInst64`.
* **The per-op Sail refinement** — `SailRiscv64Ref.rtype_{add,sub,and,or,xor}`:
  the verbatim sail-riscv `execute_RTYPE` clause writes our `RiscvModel64` op.

## What this module adds (the missing grounding)

`com_riscv_e2e` terminates at the **trusted hand-written** `evalRInst64`; nothing
tied that model back to the **proved Sail** semantics, which live in a separate
register representation (`RegFile = BitVec 5 → BitVec 64`, run via `runRd`). The
new content here is exactly that bridge, for the five ADD/SUB/AND/OR/XOR ops with
a Sail refinement:

1. **5a `riscvStep64_sail_grounded`** — for a base-ALU `RInst64`, under a
   register-name ↔ register-number alignment `RegAlign`, the value `evalRInst64`
   writes to the destination **equals the value the Sail `execute_RTYPE` clause
   writes** (`runRd …`). So each step of the model is the Sail-validated step.
2. **5b `comToRiscvLsem_correct`** — the whole-`Com` keystone: the RV64
   `runRBlock64` execution of the compiled-and-lowered base-ALU `Com` computes
   `Com.denote` (via `com_riscv_e2e`) **and** every instruction it runs is base-ALU
   (`riscvBlock_all_baseAlu`), hence every step is Sail-grounded by 5a.
3. **5c `riscvBaseAluModel`** — a genuine `MachineModel` with
   `exec := runRBlock64` (a non-`id` execution semantics) and `validated` the 5a
   grounding, inhabited by `riscvBaseAluGrounded_proof`.

## Honest scope: base-ALU only

Covered: **ADD, SUB, AND, OR, XOR** — exactly the RV64I R-type subset for which
`SailRiscv64Ref` proves `execute_RTYPE`-vs-model refinement. **Deferred:**
`MUL`/`MULHU` — `SailRiscv64Ref.rtype_mul`/`rtype_mulhu` are proved, but they go
through `execute_MUL` (a different Sail clause), so the uniform `execute_RTYPE`
grounding here does not cover them; folding them in is a mechanical extension of
`rinstRop`/the case split, left out so the base-ALU keystone stays clean. `SLTU`
(carry synthesis) is likewise not in this R-type-uniform statement.
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
open CatCrypt.Crypto.SecureCompilation.VIR.Compiler (MachineModel)

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

/-! ## 2. (5a) The Sail-grounded per-op preservation -/

/-- **5a — the per-op semantics is the Sail-validated semantics.** For a base-ALU
    `RInst64`, under a register-name alignment, the value our model `evalRInst64`
    writes to the destination equals the value the **verbatim sail-riscv
    `execute_RTYPE` clause** writes to `rd` (`runRd …`). Each arm dispatches to the
    corresponding proved `SailRiscv64Ref.rtype_*` refinement; the non-base-ALU
    arms are vacuous (`IsBaseAlu` is `False` there). This is the grounding the
    model `runRBlock64` was missing — its steps are the Sail steps. -/
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

/-! ## 3. (5b, part I) The compiled block is entirely base-ALU

So that *every* step the `runRBlock64` execution takes is Sail-grounded by 5a, we
show the lowered block of a base-ALU `Com` contains only base-ALU instructions. -/

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

/-- **The compiled-and-lowered RV64 block of a base-ALU `Com` is all base-ALU** —
    so every instruction the model executes is Sail-grounded by
    `riscvStep64_sail_grounded`. -/
theorem riscvBlock_all_baseAlu {Γ : Ctxt jasminDialect}
    {com : Com jasminDialect Γ (.reg 64)} (hba : ComBaseAlu com) :
    ∀ i ∈ lowerRBlock64 (regToROp (comToRegProg com Γ.length)), IsBaseAlu i :=
  regprog_lower_base (comToRegProg com Γ.length) (comToRegProg_RegBaseAlu hba Γ.length)

/-! ## 4. (5b) The `Com → RISC-V` value-preservation keystone -/

/-- **5b — the Sail-grounded whole-`Com` value-preservation keystone.** For a
    base-ALU all-`reg 64` `Com`, executing the compiled-and-lowered RV64 block on
    the model:

    1. **computes the source `Com.denote`** (the value chain, via the existing
       `com_riscv_e2e` — `comToReg_faithful` ∘ `compile_denote_pure_on` ∘
       `regToROp_denote`), and
    2. **runs only Sail-grounded instructions** (`riscvBlock_all_baseAlu` — every
       executed `RInst64` is base-ALU, so each step matches its `execute_RTYPE`
       clause by `riscvStep64_sail_grounded`).

    The `MachineModel.exec := id` shell of `latticeModel` is thereby replaced, on
    the base-ALU fragment, by the genuine `runRBlock64` functional semantics. -/
theorem comToRiscvLsem_correct {Γ : Ctxt jasminDialect}
    {com : Com jasminDialect Γ (.reg 64)} (hba : ComBaseAlu com) (hΓ : AllReg64 Γ)
    (V : Ctxt.Valuation Γ) (s : RState64) (hs : s.regs = envOf Γ.length V) :
    (runRBlock64 s (lowerRBlock64 (regToROp (comToRegProg com Γ.length)))).regs
        (comRetName com Γ.length)
      = Com.denote com V
    ∧ (∀ i ∈ lowerRBlock64 (regToROp (comToRegProg com Γ.length)), IsBaseAlu i) :=
  ⟨com_riscv_e2e hba.toComOK hΓ V s hs, riscvBlock_all_baseAlu hba⟩

/-! ## 5. (5c) A genuine non-`id` `exec` for the RISC-V model -/

/-- The proposition recording the per-op Sail grounding (5a), to inhabit the
    `MachineModel.validated` field — the RISC-V analogue of `VIR/Compiler.lean`'s
    `RiscvValidated`, but at the **value** (not just `decode∘encode`) depth: every
    base-ALU step of the execution semantics is the sail-riscv `execute_RTYPE`
    step. -/
def RiscvBaseAluGrounded : Prop :=
  ∀ (s : RState64) (rf : RegFile) (nm : String → BitVec 5) (i : RInst64),
    IsBaseAlu i → ¬ (rinstD i = "zero" ∨ rinstD i = "x0") → RegAlign s rf nm →
    (nm (rinstD i)).toNat ≠ 0 →
    (evalRInst64 s i).get (rinstD i)
      = runRd (execute_RTYPE ⟨nm (rinstB i)⟩ ⟨nm (rinstA i)⟩ ⟨nm (rinstD i)⟩ (rinstRop i))
          rf (nm (rinstD i))

/-- `RiscvBaseAluGrounded` is inhabited by the proved 5a theorem (not `True`). -/
theorem riscvBaseAluGrounded_proof : RiscvBaseAluGrounded :=
  fun s rf nm i hbase hdst halign hrd => riscvStep64_sail_grounded s rf nm i hbase hdst halign hrd

/-- **5c — the RISC-V base-ALU `MachineModel`, with a genuine `exec`.** Unlike
    `VIR/Compiler.lean`'s `latticeModel` (whose `exec := fun _ s => s` is a
    validation shell that does not run the code), this model's `exec` is the real
    `runRBlock64` block fold over `RState64`, and its `validated` field is the 5a
    Sail-grounding `RiscvBaseAluGrounded` (inhabited by `riscvBaseAluGrounded_proof`).
    `Code` is the executed `RInst64` list; `State`/`Value` is `RState64`. This is
    the non-`id` execution model the RISC-V path was missing for the base-ALU
    fragment. -/
def riscvBaseAluModel : MachineModel where
  Code := List RInst64
  State := RState64
  Value := RState64
  encodeIn := id
  decodeOut := id
  exec := fun code s => runRBlock64 s code
  validated := RiscvBaseAluGrounded

/-- The model's `exec` genuinely runs the code: it is `runRBlock64`, not the
    `latticeModel` identity `fun _ s => s`. -/
theorem riscvBaseAluModel_exec (code : List RInst64) (s : RState64) :
    riscvBaseAluModel.exec code s = runRBlock64 s code := rfl

/-- The model's `validated` field is the genuine 5a Sail-grounding, discharged by
    `riscvBaseAluGrounded_proof` (never `True`-by-fiat). -/
theorem riscvBaseAluModel_validated : riscvBaseAluModel.validated :=
  riscvBaseAluGrounded_proof

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.ComToRiscvLsem
