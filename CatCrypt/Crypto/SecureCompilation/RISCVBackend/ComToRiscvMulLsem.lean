/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.ComToRiscvLsem

/-!
# `Com → RISC-V`: the Sail-grounded value-preservation theorem with `MUL`/`MULHU`

`ComToRiscvLsem.lean` (item 5) grounded the RV64 base-ALU fragment
(ADD/SUB/AND/OR/XOR) in the verbatim sail-riscv `execute_RTYPE` clause and built
a non-`id` `MachineModel` (`riscvBaseAluModel`, `exec := runRBlock64`)
whose `validated` field is the per-op Sail grounding. It explicitly **deferred**
`MUL`/`MULHU`: those ops route through a *different* Sail clause
(`execute_MUL`, the M-extension `mult_to_bits_half` path), so the uniform
`execute_RTYPE` step grounding there did not reach them.

This module closes that gap. It widens the fragment to the **arith+mul** subset
— base-ALU ∪ {`MUL`, `MULHU`} — for which `SailRiscv64Ref` already proves the
two M-extension refinements (`rtype_mul`, `rtype_mulhu`).

## What is reused (not re-derived)

* **The two M-extension Sail refinements** —
  `SailRiscv64Ref.rtype_mul`/`rtype_mulhu`: the verbatim generated
  `execute_MUL` clause (with `mul_op` `⟨.Low,.Signed,.Signed⟩` resp.
  `⟨.High,.Unsigned,.Unsigned⟩`) writes our `RiscvModel64.opMul64`/`opMulhu`.
  These are already proved, through the L1/L2 BitVec lemmas
  (`mulhu_value`, `mul_value`).
* **The model semantics** — `RiscvModel64.evalRInst64` already has the
  `.mul`/`.mulhu` arms (writing `opMul64`/`opMulhu`); no definitional addition
  to `RiscvModel64` was needed (the item-5 scout's "no MUL/MULHU yet" was about
  the *grounding*, not the model — the per-op semantics and the `RInst64`
  constructors were already present).
* **The whole-`Com` value chain** — `MultiBackendDemo.com_riscv_e2e`, which
  already threads `.regArith .mul`/`.mulhi` through the front
  (`opToStmts → .mul`/`.umulh`, `regStmtToROp → .mul`/`.mulhu`,
  `toRInst64`). So the value half holds verbatim for mul/mulhu `Com`s once the
  op-set predicate (`SupportedOp`) is satisfied — and `SupportedOp` already
  admits `.regArith .mul 64` and `.mulhi 64`.
* **The base-ALU grounding** — `ComToRiscvLsem.riscvStep64_sail_grounded`, reused
  for the five base-ALU arms of the widened step grounding.

## What this module adds

1. **`sailClause`** — the per-op selector mapping each `IsArithMul` `RInst64` to
   the *actual* Sail clause it refines: `execute_RTYPE … (rinstRop i)` for the
   base-ALU arms, `execute_MUL … (rinstMulOp i)` for `MUL`/`MULHU`. This is the
   uniform selector across the two Sail clauses.
2. **`riscvStepArithMul_sail_grounded`** (the widened 5a) — for any `IsArithMul`
   `RInst64`, the value `evalRInst64` writes to the destination equals the value
   its `sailClause` writes (`runRd …`). The base-ALU arms dispatch to
   `riscvStep64_sail_grounded`; the `MUL`/`MULHU` arms dispatch to
   `rtype_mul`/`rtype_mulhu`.
3. **`comToRiscvLsem_correct_mul`** (the widened 5b) — the whole-`Com` theorem
   over the arith+mul `Com` fragment (`ComArithMul`): the RV64 `runRBlock64`
   execution computes `Com.denote` (via `com_riscv_e2e`) **and** every executed
   instruction is `IsArithMul`, hence Sail-grounded by the widened 5a.
4. **`riscvArithMulModel`** (the widened 5c) — the non-`id`
   `MachineModel` (`exec := runRBlock64`) whose `validated` field is the widened
   grounding `RiscvArithMulGrounded`, inhabited by the proved step lemma.

## Scope

Covered: **ADD, SUB, AND, OR, XOR, MUL, MULHU** — the base-ALU R-type subset
plus the two M-extension ops with an `execute_MUL` refinement. `MUL` is grounded
at signedness `⟨.Low,.Signed,.Signed⟩` (the low half is signedness-independent,
per `mul_value`); `MULHU` at `⟨.High,.Unsigned,.Unsigned⟩` (the bignum
high-word primitive). Signed high-multiply variants (`MULH`/`MULHSU`),
`SLTU` (carry synthesis), the shifts, and `LI`/`MV` remain outside this
statement.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend.ComToRiscvMulLsem

open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RegToRiscv
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscv64Ref
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.ComToRiscvLsem
open CatCrypt.Crypto.SecureCompilation.ScalarLin
open CatCrypt.Crypto.SecureCompilation.ScalarLinFront
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
open CatCrypt.Crypto.SecureCompilation.MultiBackendDemo
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.Compiler (MachineModel)

/-! ## 1. The arith+mul fragment (base-ALU ∪ {MUL, MULHU}) -/

/-- An arith+mul `RInst64`: the base-ALU R-type ops (`execute_RTYPE` refinement)
    together with the two M-extension ops with an `execute_MUL` refinement
    (`MUL`/`MULHU`). The remaining ops (`SLTU`, `LI`, `MV`, shifts) are not in
    this fragment. -/
def IsArithMul : RInst64 → Prop
  | .add .. | .sub .. | .and .. | .or .. | .xor .. | .mul .. | .mulhu .. => True
  | _ => False

/-- The `mul_op` a `MUL`/`MULHU` `RInst64` selects in `execute_MUL`: `MUL` takes
    the low half (signedness-independent, fixed to `Signed`/`Signed` matching
    `rtype_mul`); `MULHU` takes the high half of the unsigned product. Non-mul
    arms are irrelevant (the default `⟨.Low,.Signed,.Signed⟩` is never used by
    the grounding — those arms route through `execute_RTYPE`). -/
def rinstMulOp : RInst64 → mul_op
  | .mul ..   => ⟨.Low, .Signed, .Signed⟩
  | .mulhu .. => ⟨.High, .Unsigned, .Unsigned⟩
  | _         => ⟨.Low, .Signed, .Signed⟩

/-- The destination register name of an arith+mul `RInst64` (extends `rinstD`
    over the `MUL`/`MULHU` arms). -/
def amD : RInst64 → String
  | .add d _ _ | .sub d _ _ | .and d _ _ | .or d _ _ | .xor d _ _
  | .mul d _ _ | .mulhu d _ _ => d
  | _ => ""

/-- The first source register name (extends `rinstA`). -/
def amA : RInst64 → String
  | .add _ a _ | .sub _ a _ | .and _ a _ | .or _ a _ | .xor _ a _
  | .mul _ a _ | .mulhu _ a _ => a
  | _ => ""

/-- The second source register name (extends `rinstB`). -/
def amB : RInst64 → String
  | .add _ _ b | .sub _ _ b | .and _ _ b | .or _ _ b | .xor _ _ b
  | .mul _ _ b | .mulhu _ _ b => b
  | _ => ""

/-- **The per-op Sail clause selector.** Each arith+mul `RInst64` refines a
    *specific* generated sail-riscv clause: base-ALU ops the `execute_RTYPE`
    clause (selecting `rinstRop i`), `MUL`/`MULHU` the `execute_MUL` clause
    (selecting `rinstMulOp i`). Register numbers come through the name map `nm`.
    This is the uniform selector — the grounding statement below is uniform across
    *both* clauses through this selector. -/
def sailClause (nm : String → BitVec 5) : RInst64 → SailM ExecutionResult
  | .mul d a b =>
      execute_MUL ⟨nm b⟩ ⟨nm a⟩ ⟨nm d⟩ ⟨.Low, .Signed, .Signed⟩
  | .mulhu d a b =>
      execute_MUL ⟨nm b⟩ ⟨nm a⟩ ⟨nm d⟩ ⟨.High, .Unsigned, .Unsigned⟩
  | i => execute_RTYPE ⟨nm (rinstB i)⟩ ⟨nm (rinstA i)⟩ ⟨nm (rinstD i)⟩ (rinstRop i)

/-- On the base-ALU arms, `amD`/`amA`/`amB` agree with the base-ALU
    `rinstD`/`rinstA`/`rinstB`. (Trivial; used to reuse the base-ALU grounding.) -/
theorem baseAlu_names {i : RInst64} (h : IsBaseAlu i) :
    amD i = rinstD i ∧ amA i = rinstA i ∧ amB i = rinstB i := by
  cases i <;> simp_all [IsBaseAlu, amD, amA, amB, rinstD, rinstA, rinstB]

/-- A base-ALU `RInst64` is arith+mul. -/
theorem IsBaseAlu.toArithMul {i : RInst64} (h : IsBaseAlu i) : IsArithMul i := by
  cases i <;> simp_all [IsBaseAlu, IsArithMul]

/-! ## 2. The widened (5a) step grounding -/

/-- **5a (widened) — every arith+mul step is its Sail-validated step.** For an
    `IsArithMul` `RInst64`, under a register-name alignment, the value
    `evalRInst64` writes to the destination equals the value the op's *actual*
    Sail clause (`sailClause`) writes to `rd` (`runRd …`):

    * the five base-ALU arms reuse `riscvStep64_sail_grounded` (the
      `execute_RTYPE` grounding from item 5);
    * the `MUL` arm dispatches to `rtype_mul` (`execute_MUL` low, signed);
    * the `MULHU` arm dispatches to `rtype_mulhu` (`execute_MUL` high, unsigned).

    The non-arith+mul arms are vacuous (`IsArithMul` is `False`). This is the
    grounding the widened `runRBlock64` model was missing for the M-extension. -/
theorem riscvStepArithMul_sail_grounded
    (s : RState64) (rf : RegFile) (nm : String → BitVec 5) (i : RInst64)
    (ham : IsArithMul i)
    (hdst : ¬ (amD i = "zero" ∨ amD i = "x0"))
    (halign : RegAlign s rf nm)
    (hrd : (nm (amD i)).toNat ≠ 0) :
    (evalRInst64 s i).get (amD i) = runRd (sailClause nm i) rf (nm (amD i)) := by
  -- Base-ALU arms: reuse the item-5 grounding through `sailClause = execute_RTYPE`.
  have base : ∀ j : RInst64, IsBaseAlu j →
      ¬ (rinstD j = "zero" ∨ rinstD j = "x0") → (nm (rinstD j)).toNat ≠ 0 →
      (evalRInst64 s j).get (rinstD j)
        = runRd (execute_RTYPE ⟨nm (rinstB j)⟩ ⟨nm (rinstA j)⟩ ⟨nm (rinstD j)⟩ (rinstRop j))
            rf (nm (rinstD j)) :=
    fun j hj hdj hrj => riscvStep64_sail_grounded s rf nm j hj hdj halign hrj
  cases i with
  | add d a b =>
      have e := base (.add d a b) trivial (by simpa [amD] using! hdst) (by simpa [amD] using! hrd)
      exact e
  | sub d a b =>
      have e := base (.sub d a b) trivial (by simpa [amD] using! hdst) (by simpa [amD] using! hrd)
      exact e
  | and d a b =>
      have e := base (.and d a b) trivial (by simpa [amD] using! hdst) (by simpa [amD] using! hrd)
      exact e
  | or d a b =>
      have e := base (.or d a b) trivial (by simpa [amD] using! hdst) (by simpa [amD] using! hrd)
      exact e
  | xor d a b =>
      have e := base (.xor d a b) trivial (by simpa [amD] using! hdst) (by simpa [amD] using! hrd)
      exact e
  | mul d a b =>
      have hrd' : (nm d).toNat ≠ 0 := by simpa [amD] using hrd
      have hdst' : ¬ (d = "zero" ∨ d = "x0") := by simpa [amD] using hdst
      simp only [amD, sailClause, evalRInst64,
        RState64.get_set_same _ _ _ hdst']
      rw [rtype_mul rf (nm a) (nm b) (nm d) hrd', halign a, halign b]
  | mulhu d a b =>
      have hrd' : (nm d).toNat ≠ 0 := by simpa [amD] using hrd
      have hdst' : ¬ (d = "zero" ∨ d = "x0") := by simpa [amD] using hdst
      simp only [amD, sailClause, evalRInst64,
        RState64.get_set_same _ _ _ hdst']
      rw [rtype_mulhu rf (nm a) (nm b) (nm d) hrd', halign a, halign b]
  | sltu d a b => exact absurd ham (by simp [IsArithMul])
  | li d imm => exact absurd ham (by simp [IsArithMul])
  | mv d a => exact absurd ham (by simp [IsArithMul])
  | srli d a sh => exact absurd ham (by simp [IsArithMul])
  | slli d a sh => exact absurd ham (by simp [IsArithMul])

/-! ## 3. (5b, part I) The compiled arith+mul block is entirely arith+mul -/

/-- A `RegStmt` whose RV64 selection + lowering is the arith+mul fragment: the
    base-ALU ops plus `.mul` (→ `MUL`) and `.umulh` (→ `MULHU`). -/
def RegArithMul : RegStmt → Prop
  | .add .. | .sub .. | .and .. | .orr .. | .eor .. | .mul .. | .umulh .. => True
  | _ => False

/-- One arith+mul `RegStmt` lowers (`regStmtToROp` then `toRInst64`) to all
    arith+mul `RInst64`s. -/
theorem stmt_lower_arithMul (stmt : RegStmt) (h : RegArithMul stmt) :
    ∀ i ∈ (regStmtToROp stmt).flatMap toRInst64, IsArithMul i := by
  cases stmt <;> simp_all [RegArithMul, regStmtToROp, toRInst64, IsArithMul]

/-- A whole arith+mul `RegProg` lowers to an all-arith+mul `RInst64` block. -/
theorem regprog_lower_arithMul (p : RegProg) (hp : ∀ stmt ∈ p, RegArithMul stmt) :
    ∀ i ∈ lowerRBlock64 (regToROp p), IsArithMul i := by
  intro i hi
  rw [show lowerRBlock64 (regToROp p) = (p.flatMap regStmtToROp).flatMap toRInst64 from rfl,
      List.flatMap_assoc, List.mem_flatMap] at hi
  obtain ⟨stmt, hstmt, hi'⟩ := hi
  exact stmt_lower_arithMul stmt (hp stmt hstmt) i hi'

/-! ### The `Com`-level arith+mul restriction -/

/-- A `JasminOp` in the arith+mul fragment: base-ALU `regArith` ops, `regArith
    .mul 64`, or `mulhi 64` (the front's `MULHU` source). -/
def ArithMulOp (op : JasminOp) : Prop :=
  (∃ bop, op = JasminOp.regArith bop 64 ∧
    (bop = .add ∨ bop = .sub ∨ bop = .and ∨ bop = .or ∨ bop = .xor ∨ bop = .mul))
  ∨ op = JasminOp.mulhi 64

/-- An arith+mul op is a `SupportedOp` (so `com_riscv_e2e` applies). -/
theorem ArithMulOp.toSupported {op : JasminOp} (h : ArithMulOp op) : SupportedOp op := by
  rcases h with ⟨bop, rfl, hbop⟩ | rfl
  · refine Or.inl ⟨bop, rfl, ?_⟩
    rcases hbop with h|h|h|h|h|h <;> subst h <;> tauto
  · exact Or.inr (Or.inl rfl)

/-- An arith+mul op selects only arith+mul `RegStmt`s. -/
theorem opToStmts_arithMul (d : String) (srcs : List String) (op : JasminOp)
    (hop : ArithMulOp op) : ∀ stmt ∈ opToStmts d srcs op, RegArithMul stmt := by
  rcases hop with ⟨bop, rfl, hbop⟩ | rfl
  · rcases hbop with h|h|h|h|h|h <;> subst h <;>
      (rcases srcs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp_all [opToStmts, RegArithMul])
  · rcases srcs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp_all [opToStmts, RegArithMul]

/-- The straight-line `Com` fragment whose every op is arith+mul (a sub-fragment
    of `ScalarLinDeBruijn.ComOK`). -/
inductive ComArithMul : {Γ : Ctxt jasminDialect} → Com jasminDialect Γ (.reg 64) → Prop where
  /-- A `.ret` is arith+mul. -/
  | ret {Γ : Ctxt jasminDialect} (v : Ctxt.Var Γ (.reg 64)) : ComArithMul (.ret v)
  /-- A `.var` whose op is arith+mul, over an arith+mul body. -/
  | var {Γ : Ctxt jasminDialect} {e : Expr jasminDialect Γ (.reg 64)}
      {body : Com jasminDialect ((.reg 64) :: Γ) (.reg 64)}
      (hb : ArithMulOp e.op) (hbody : ComArithMul body) : ComArithMul (.var e body)

/-- An arith+mul `Com` is a supported `Com` (the hypothesis `com_riscv_e2e` needs). -/
theorem ComArithMul.toComOK : ∀ {Γ : Ctxt jasminDialect} {com : Com jasminDialect Γ (.reg 64)},
    ComArithMul com → ComOK com := by
  intro Γ com h
  induction h with
  | ret v => exact ComOK.ret v
  | var hb hbody ih => exact ComOK.var hb.toSupported ih

/-- **Every statement the front emits from an arith+mul `Com` is `RegArithMul`.** -/
theorem comToRegProg_RegArithMul :
    ∀ {Γ : Ctxt jasminDialect} {com : Com jasminDialect Γ (.reg 64)},
      ComArithMul com → ∀ (depth : Nat), ∀ stmt ∈ comToRegProg com depth, RegArithMul stmt := by
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
      · exact opToStmts_arithMul _ _ _ hb stmt hh
      · exact ih (depth + 1) stmt hh

/-- **The compiled-and-lowered RV64 block of an arith+mul `Com` is all arith+mul**
    — so every executed instruction is Sail-grounded by
    `riscvStepArithMul_sail_grounded`. -/
theorem riscvBlock_all_arithMul {Γ : Ctxt jasminDialect}
    {com : Com jasminDialect Γ (.reg 64)} (ham : ComArithMul com) :
    ∀ i ∈ lowerRBlock64 (regToROp (comToRegProg com Γ.length)), IsArithMul i :=
  regprog_lower_arithMul (comToRegProg com Γ.length) (comToRegProg_RegArithMul ham Γ.length)

/-! ## 4. (5b widened) The `Com → RISC-V` value-preservation theorem -/

/-- **5b (widened) — the Sail-grounded whole-`Com` theorem over base-ALU ∪
    {MUL, MULHU}.** For an arith+mul all-`reg 64` `Com`, executing the
    compiled-and-lowered RV64 block on the model:

    1. **computes the source `Com.denote`** (the value chain, via the existing
       `com_riscv_e2e` — the front already threads `.regArith .mul`/`.mulhi`), and
    2. **runs only Sail-grounded instructions** (`riscvBlock_all_arithMul` —
       every executed `RInst64` is arith+mul, so each step matches its actual
       Sail clause by `riscvStepArithMul_sail_grounded`: `execute_RTYPE` for the
       base-ALU ops, `execute_MUL` for `MUL`/`MULHU`).

    This widens `ComToRiscvLsem.comToRiscvLsem_correct` from the base-ALU subset
    to the arith+mul subset, the M-extension included. -/
theorem comToRiscvLsem_correct_mul {Γ : Ctxt jasminDialect}
    {com : Com jasminDialect Γ (.reg 64)} (ham : ComArithMul com) (hΓ : AllReg64 Γ)
    (V : Ctxt.Valuation Γ) (s : RState64) (hs : s.regs = envOf Γ.length V) :
    (runRBlock64 s (lowerRBlock64 (regToROp (comToRegProg com Γ.length)))).regs
        (comRetName com Γ.length)
      = Com.denote com V
    ∧ (∀ i ∈ lowerRBlock64 (regToROp (comToRegProg com Γ.length)), IsArithMul i) :=
  ⟨com_riscv_e2e ham.toComOK hΓ V s hs, riscvBlock_all_arithMul ham⟩

/-! ## 5. (5c widened) A non-`id` `exec` for the arith+mul model -/

/-- The proposition recording the per-op Sail grounding (widened 5a), to inhabit
    the `MachineModel.validated` field at value depth: every arith+mul step of
    the execution semantics is the sail-riscv step (`execute_RTYPE` for base-ALU,
    `execute_MUL` for `MUL`/`MULHU`), via the `sailClause` selector. -/
def RiscvArithMulGrounded : Prop :=
  ∀ (s : RState64) (rf : RegFile) (nm : String → BitVec 5) (i : RInst64),
    IsArithMul i → ¬ (amD i = "zero" ∨ amD i = "x0") → RegAlign s rf nm →
    (nm (amD i)).toNat ≠ 0 →
    (evalRInst64 s i).get (amD i) = runRd (sailClause nm i) rf (nm (amD i))

/-- `RiscvArithMulGrounded` is inhabited by the proved widened-5a theorem
    (not `True`). -/
theorem riscvArithMulGrounded_proof : RiscvArithMulGrounded :=
  fun s rf nm i ham hdst halign hrd =>
    riscvStepArithMul_sail_grounded s rf nm i ham hdst halign hrd

/-- **5c (widened) — the RISC-V arith+mul `MachineModel`, with a non-`id` `exec`.**
    Like `ComToRiscvLsem.riscvBaseAluModel`, its `exec` is the
    `runRBlock64` block fold (not `latticeModel`'s `fun _ s => s`), and its
    `validated` field is the widened Sail-grounding `RiscvArithMulGrounded`
    (inhabited by `riscvArithMulGrounded_proof`), covering the M-extension
    ops `MUL`/`MULHU` in addition to the base ALU. -/
def riscvArithMulModel : MachineModel where
  Code := List RInst64
  State := RState64
  Value := RState64
  encodeIn := id
  decodeOut := id
  exec := fun code s => runRBlock64 s code
  validated := RiscvArithMulGrounded

/-- The model's `exec` is `runRBlock64`, not the `latticeModel` identity. -/
theorem riscvArithMulModel_exec (code : List RInst64) (s : RState64) :
    riscvArithMulModel.exec code s = runRBlock64 s code := rfl

/-- The model's `validated` field is the widened-5a Sail-grounding,
    discharged by `riscvArithMulGrounded_proof`. -/
theorem riscvArithMulModel_validated : riscvArithMulModel.validated :=
  riscvArithMulGrounded_proof

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.ComToRiscvMulLsem
