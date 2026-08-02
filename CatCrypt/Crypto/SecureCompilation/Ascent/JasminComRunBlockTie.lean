/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel
import CatCrypt.Crypto.Optimizer.RandomizedRegAlloc

/-!
# The single-op `Com jasminDialect` ↔ `runBlock` tie (register-allocation core)

This module builds the **core** of the "D" correspondence between the typed SSA
substrate (`Com jasminDialect`, VIR) and the register-machine (`JState`/`runBlock`,
the faithful Jasmin x86 transcription): the value spine of a single
register-arithmetic op agrees on both sides, tied by a state correspondence
`JStateInterp` (the machine register file holds the SSA valuation's values).

## What is proved

* `JStateInterp` — the state correspondence: for every `reg 64` SSA variable `v`
  in context `Γ`, the machine register `ρ v` holds the valuation value `v.lookup V`.
  This is the `Com`-valuation analogue of `LowCTToJInstrCT.StateMatch`, but on the
  **BitVec value spine** (`Ctxt.Valuation` ↔ `JState`) directly — never routed
  through `RustState`/`Nat` (which would saturate).
* `jasminBop_eq_machine` — **the value agreement**: for a scalar `JasminBinOp`
  (`add`/`sub`/`and`/`or`/`xor`/`mul` — the arms whose `JasminBinOp.apply` is a
  plain `BitVec 64` op with no shift-count mask), the machine instruction the
  lowering picks computes exactly `bop.apply (s.get dst) (s.get rb)`. Both the
  dialect denotation and the machine step reduce to the *same* `BitVec 64` op.
* `jasminSingleOp_denote` — the dialect side: the single-op `regArith bop`
  `Com` denotes to `bop.apply (V a) (V b)`, a genuine value read from `V`.
* `jasminOp_runBlock_tie` — **the tie**: reading the destination register after
  running the lowered `mov; op` block equals the `Com`'s denotation on `V`.

## Composition to the general case

The single-op tie fixes the *value agreement* + the *state correspondence*.
Register **allocation** — that a physical-register renaming preserves the whole
block's `runBlock` — is `Optimizer.RandomizedRegAlloc.regalloc_runBlock_sound`
(imported, cited below in `regalloc_composition_note`). The general
`Com jasminDialect → JState` correspondence composes the two: this file supplies
the per-op value leg, regalloc supplies the allocation leg.

## Model split (compiler skill)

The value spine here is `BitVec 64` on both sides. `JStateInterp` relates
`Ctxt.Valuation Γ` (BitVec) ↔ `JState 64` (BitVec) directly, so the tie is on
real machine words, not the saturating `RustState`/`Nat` model.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## 1. The single-op `Com jasminDialect`

The two-input register-arithmetic context and the one-op program
`let s = regArith bop a b in ret s`, mirroring `JasminDialect.smokeProg`. -/

/-- The two-input `reg 64` context. -/
abbrev Γ2 : Ctxt jasminDialect := [.reg 64, .reg 64]

/-- The first operand variable (de Bruijn 0). -/
abbrev vA : Ctxt.Var Γ2 (.reg 64) := .here

/-- The second operand variable (de Bruijn 1). -/
abbrev vB : Ctxt.Var Γ2 (.reg 64) := .there .here

/-- The single-op program `let s = regArith bop a b in ret s : Com jasminDialect`
    over `[reg 64, reg 64]`. Built exactly like `JasminDialect.smokeProg`'s first
    op: the `regArith bop 64` op applied to the two context variables. -/
def jasminSingleOp (bop : JasminBinOp) : Com jasminDialect Γ2 (.reg 64) :=
  .var (.mk (.regArith bop 64) rfl (.cons vA (.cons vB .nil)))
    (.ret .here)

/-- **The dialect side.** The single-op `Com` denotes to `bop.apply (V a) (V b)`,
    a genuine value read from the valuation `V`. Reduces definitionally through
    `Com.denote`/`Expr.denote`/`lookupArgs` and the `regArith` arm of
    `jasminDenote`. -/
theorem jasminSingleOp_denote (bop : JasminBinOp) (V : Ctxt.Valuation Γ2) :
    (jasminSingleOp bop).denote V = bop.apply (vA.lookup V) (vB.lookup V) := by
  rfl

/-! ## 2. The scalar op subset and its machine lowering -/

/-- The `JasminBinOp` arms whose `apply` is a plain `BitVec 64` op with **no**
    shift-count mask: `add/sub/and/or/xor/mul`. For these the dialect denotation
    and the machine ALU step compute the *same* `BitVec` op. `shl`/`shr` are
    excluded — the machine `x86_SHL`/`x86_SHR` mask the count `mod 64` and read it
    from a register, so they agree with `apply` only for in-range amounts; `andn`
    has no single two-address instruction in the emitted subset. -/
def IsScalarBop : JasminBinOp → Prop
  | .add | .sub | .and | .or | .xor | .mul => True
  | _ => False

/-- The machine two-address instruction for a scalar `JasminBinOp`, applied to
    destination `dst` with second operand `src`. The `mov dst ra` primes `dst`
    with the first operand, then this op does `dst := dst ⟨bop⟩ src`. The `.shl`/
    `.shr`/`.andn` arms are placeholders (never reached under `IsScalarBop`). -/
def bopToJInstr (bop : JasminBinOp) (dst : String) (src : JOperand) : JInstr 64 :=
  match bop with
  | .add => .add dst src
  | .sub => .sub dst src
  | .and => .and_ dst src
  | .or  => .or_ dst src
  | .xor => .xor_ dst src
  | .mul => .imul dst src
  | .shl => .shl dst src
  | .shr => .shr dst src
  | .andn => .mov dst src

/-- The per-variable register map: an `SSA reg 64` variable to a machine register
    name. A genuine register allocation assigns distinct physical registers to
    simultaneously-live slots; we keep it abstract and constrain it only where the
    tie needs it (the destination must differ from the second-operand register). -/
abbrev RegMap := Ctxt.Var Γ2 (.reg 64) → String

/-- **The lowering.** The single-op program lowers to the two-instruction block
    `mov dst ρa; op dst ρb`. Memory-free (register `mov` + a register-operand
    ALU op), so it is trivially in the machine constant-time class. -/
def lowerJasminArith (bop : JasminBinOp) (ρ : RegMap) (dst : String) :
    List (JInstr 64) :=
  [ .mov dst (.reg (ρ vA))
  , bopToJInstr bop dst (.reg (ρ vB)) ]

/-! ## 3. The value agreement (`bop.apply` = machine word op) -/

/-- **The value agreement.** For a scalar `JasminBinOp`, running the chosen
    machine instruction writes to `dst` exactly `bop.apply (s.get dst) (s.get rb)`
    — the *same* `BitVec 64` op that the dialect's `regArith bop` denotes. This is
    the per-op tie between the dialect semantics (`JasminBinOp.apply`) and the
    faithful x86 model's data word (`x86_ADD`/`x86_SUB`/`x86_AND`/… `.word`). -/
theorem jasminBop_eq_machine (bop : JasminBinOp) (hbop : IsScalarBop bop)
    (dst rb : String) (s : JState 64) :
    (evalInstr s (bopToJInstr bop dst (.reg rb))).get dst
      = bop.apply (s.get dst) (s.get rb) := by
  cases bop <;>
    simp_all [IsScalarBop, bopToJInstr, JasminBinOp.apply, evalInstr,
      x86_ADD, x86_SUB, x86_AND, x86_OR, x86_XOR, x86_IMULt,
      rflags_of_aluop, rflags_of_bwop, rflags_of_mul, JState.writeB5W, JState.get]

/-- The chosen op writes only its destination: reading any other register `r ≠ dst`
    after the op falls through unchanged. -/
theorem bopToJInstr_get_other (bop : JasminBinOp) (hbop : IsScalarBop bop)
    (dst rb r : String) (s : JState 64) (hr : r ≠ dst) :
    (evalInstr s (bopToJInstr bop dst (.reg rb))).get r = s.get r := by
  cases bop <;>
    simp_all [IsScalarBop, bopToJInstr, evalInstr,
      x86_ADD, x86_SUB, x86_AND, x86_OR, x86_XOR, x86_IMULt,
      rflags_of_aluop, rflags_of_bwop, rflags_of_mul, JState.writeB5W, JState.get]

/-! ## 4. The state correspondence `JStateInterp` -/

/-- **The state correspondence.** The machine register `ρ v` holds the SSA
    valuation's value `v.lookup V`, for **every** `reg 64` variable `v` in the
    context. This is the `Com`-valuation analogue of `LowCTToJInstrCT.StateMatch`,
    on the BitVec value spine (`Ctxt.Valuation` ↔ `JState 64`) — no `RustState`,
    no `Nat` saturation. -/
def JStateInterp (ρ : RegMap) (V : Ctxt.Valuation Γ2) (s : JState 64) : Prop :=
  ∀ v : Ctxt.Var Γ2 (.reg 64), s.get (ρ v) = v.lookup V

/-! ## 5. The tie -/

/-- **The single-op `.denote ↔ runBlock` tie.** Under the state correspondence
    `JStateInterp ρ V s` and the register-allocation side-condition that the
    destination register differs from the second-operand register
    (`dst ≠ ρ vB` — so the priming `mov dst ρa` does not clobber the `b` read),
    reading `dst` after running the lowered block equals the `Com`'s denotation on
    `V`. Both sides are `bop.apply (V a) (V b)`: the LHS a real register read after
    a real `runBlock`, the RHS a real dialect denotation of the two valuation
    values — no vacuity. -/
theorem jasminOp_runBlock_tie (bop : JasminBinOp) (hbop : IsScalarBop bop)
    (ρ : RegMap) (dst : String) (s : JState 64) (V : Ctxt.Valuation Γ2)
    (hinterp : JStateInterp ρ V s) (hdst : dst ≠ ρ vB) :
    (runBlock s (lowerJasminArith bop ρ dst)).get dst = (jasminSingleOp bop).denote V := by
  rw [jasminSingleOp_denote]
  -- `runBlock` over the two-instruction block reduces to `evalInstr ∘ evalInstr`.
  simp only [lowerJasminArith, runBlock_cons, runBlock_nil]
  -- The op writes `bop.apply (dst') (rb')` where `dst'`/`rb'` are the reads after
  -- the priming `mov dst ρa`.
  rw [jasminBop_eq_machine bop hbop]
  have hne : ρ vB ≠ dst := fun h => hdst h.symm
  -- After the `mov dst ρa`, `dst` holds `s.get (ρ a)` and `ρ b` is untouched.
  have hmov_dst : (evalInstr s (.mov dst (.reg (ρ vA)))).get dst = s.get (ρ vA) := by
    simp [evalInstr, x86_MOV, JOperand.eval, JState.setReg, JState.get]
  have hmov_rb : (evalInstr s (.mov dst (.reg (ρ vA)))).get (ρ vB) = s.get (ρ vB) := by
    simp [evalInstr, x86_MOV, JOperand.eval, JState.setReg, JState.get, hne]
  rw [hmov_dst, hmov_rb, hinterp vA, hinterp vB]

/-! ## 6. Non-vacuity witness

A concrete instance of the tie, evaluated on both sides to a real `BitVec 64`
value, demonstrates neither side collapses to `default`: `7 + 35 = 42`. -/

/-- Concrete valuation `⟨7, 35⟩`. -/
def sampleV : Ctxt.Valuation Γ2 := .cons (7 : BitVec 64) (.cons (35 : BitVec 64) .nil)

/-- Concrete machine state whose registers `"a"`/`"b"` hold `7`/`35`. -/
def sampleS : JState 64 :=
  { regs := fun r => if r = "a" then 7 else if r = "b" then 35 else 0 }

/-- The concrete register map: `vA ↦ "a"`, `vB ↦ "b"`. -/
def sampleρ : RegMap := fun v =>
  match v with
  | .here => "a"
  | .there .here => "b"

/-- The dialect side computes the genuine value `7 + 35 = 42`. -/
example : (jasminSingleOp .add).denote sampleV = (42 : BitVec 64) := by rfl

/-- The machine side (running `mov d a; add d b` and reading `d`) computes `42`. -/
example :
    (runBlock sampleS (lowerJasminArith .add sampleρ "d")).get "d" = (42 : BitVec 64) := by
  rfl

/-- The tie holds on the concrete instance: both sides are `42`. -/
example :
    (runBlock sampleS (lowerJasminArith .add sampleρ "d")).get "d"
      = (jasminSingleOp .add).denote sampleV := by
  refine jasminOp_runBlock_tie .add trivial sampleρ "d" sampleS sampleV ?_ (by decide)
  intro v
  match v with
  | .here => rfl
  | .there .here => rfl

/-! ## 7. Composition with register allocation

The single-op tie above is the **value leg** of the general
`Com jasminDialect → JState` correspondence. The **allocation leg** — that a
physical-register renaming `ρ` preserves a whole block's `runBlock` — is
`Optimizer.RandomizedRegAlloc.regalloc_runBlock_sound`
(`StateRel ρ (runBlock (renameState σ s) (renameBlock ρ block)) (runBlock s block)`
for injective `ρ` with left inverse `σ`). The general tie composes the two: this
file's per-op value agreement with regalloc's block-level renaming soundness.
The lemma below is a direct re-export witnessing the imported reference. -/

/-- Re-export of the register-allocation soundness leg (see module docstring):
    renaming the physical registers of a block preserves its `runBlock` up to the
    bijection `ρ`. Composes with `jasminOp_runBlock_tie` for the general
    `Com`↔machine correspondence. -/
theorem regalloc_composition_note {ρ σ : String → String}
    (hρ : Function.Injective ρ) (hσ : Function.LeftInverse σ ρ)
    (block : List (JInstr 64)) (s : JState 64) :
    CatCrypt.Crypto.Optimizer.RandomizedRegAlloc.StateRel ρ
      (runBlock (CatCrypt.Crypto.Optimizer.RandomizedRegAlloc.renameState σ s)
        (CatCrypt.Crypto.Optimizer.RandomizedRegAlloc.renameBlock ρ block))
      (runBlock s block) :=
  CatCrypt.Crypto.Optimizer.RandomizedRegAlloc.regalloc_runBlock_sound hρ hσ block s

end CatCrypt.Crypto.SecureCompilation.Ascent
