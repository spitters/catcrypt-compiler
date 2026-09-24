/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Core
public import CatCrypt.Crypto.SecureCompilation.VIR.Core
public import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel

/-!
# The x86 backend as a VIR/MLIR `Com` dialect

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

`JasminModel.lean` is a faithful Lean transcription of Jasmin's Rocq x86
instruction semantics for the emitted scalar+ADX subset (the `x86_*` semantic
functions, the five-flag `JFlag` state, `evalInstr`/`runBlock`), differentially
validated against the compiled Rocq model in `TranslationValidation.lean`. This
module lifts that semantics into the project's dialect substrate (the
lean-mlir/Veir `Dialect := {Op, Ty}` abstraction with `DialectSignature` and
`DialectDenote`, in `VIR/Core.lean`), so the backend step becomes a typed `Com`
whose denotation IS the Jasmin port.

## The dialect (`x86Dialect`)

* **`Ty = X86Ty`** has one inhabitant `machine w` denoting to `JState w`
  (the faithful register-file + five-flag state of `JasminModel`). The machine
  state is a *dialect value*: a `Com x86Dialect [machine w] (machine w)` is a
  state transformer `JState w → JState w`.
* **`Op = X86Op w`** is the ported scalar+ADX instruction set `JInstr w`. Each
  op takes one operand `machine w` (the incoming state) and returns one
  `machine w` (the outgoing state).

This is the **state-passing** encoding the framework already uses to fit a
register machine onto a pure-SSA `Com` (the `BState` register-file precedent in
`VIR/ChaChaEmit.lean`, which threads register-name → SSA-var bindings while
building a pure `Com`): here the *whole* `JState` is threaded as the dialect's
value, so each op denotes straight to `JasminModel.evalInstr` and a straight-line
`Com` chain denotes to `JasminModel.runBlock`.

## `DialectDenote`

`DialectDenote x86Dialect`'s `denote (X86Op.instr i) ⟨s⟩ = evalInstr s i` — the
per-op denotation is *exactly* `JasminModel.evalInstr`, the `eval_op`/
`exec_instr_op` composition transcribed from `arch_sem.v`. No new semantics is
introduced; the dialect is a thin typed wrapper over the validated port.

## Lowering + preservation

`lowerBlock` lowers a straight-line block `List (JInstr w)` to a
`Com x86Dialect [machine w] (machine w)`, mirroring `ComToVeir_JasminDialect`'s
`Com`-building shape. `lowerBlock_denote` proves the lowered `Com`'s denotation
equals `runBlock` on the source block — for **all** straight-line blocks, by
induction. The concrete payoff `mulxAdcxAdox_lowering_correct` instantiates this
on the real emitted `#MULX → #ADCX → #ADOX` carry-chain block from
`TranslationValidation.lean` (the `mpn_addmul_1` inner-loop multiply), pinning
the lowered-and-denoted machine state to the rocq-validated Jasmin output.

## `jasminDialect` vs `x86Dialect`: complementary layers, not redundant

These two dialects are **distinct layers**, not duplicates. `jasminDialect`
(`VIR/JasminDialect.lean`) is the Rocq/emit-level *machine* dialect: the
word-level, register/stack, two-address Jasmin fragment that `RustEmitJazz`
emits, whose intended sink is a `.jazz` program via the printer. `x86Dialect`
(this file) is the validated *x86-instruction-semantics* dialect: a thin typed
wrapper over the faithful Jasmin-Rocq-model port (`JasminModel.evalInstr` /
`runBlock`, differentially validated in `TranslationValidation.lean`), serving
as the backend-validation layer one level below jasmin. The former describes
what we emit; the latter pins down what the emitted x86 *means* against the
validated model. Keep both.

## Trust story (precise)

`x86Dialect` denotes via the faithful Jasmin port (`evalInstr`/`runBlock`); it
makes **no** "authoritative / axiom-free" claim. `lowerBlock_denote` shows the
backend's straight-line lowering step is *denotation-preserving* into that
dialect. The emitted subset includes word-granular memory operands (the reg-ptr
ABI's `loadMem`/`storeMem` and the memory-source `mulxMem`); control flow and the
SIMD/AVX subset are out of scope (the source `JInstr` is the straight-line
scalar+ADX subset); a general lowering from jasmin's `Linear.lprog` with control
flow into a multi-block `Com` is outside this module's scope (§10).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## 1. Types -/

/-- The x86 dialect's value-type alphabet. The single carrier is the machine
    state at width `w` (register file + five-flag map), so a
    `Com x86Dialect [machine w] (machine w)` is a `JState w → JState w`
    transformer. -/
inductive X86Ty where
  /-- The faithful machine state at width `w` (`JasminModel.JState w`). -/
  | machine (w : Nat)
  deriving DecidableEq

/-- Total denotation of `X86Ty` into Lean types: `machine w ↦ JState w`. -/
@[reducible] instance : TyDenote X86Ty where
  denote
    | .machine w => JState w

/-! ## 2. Op tags -/

/-- The x86 dialect's operations, parameterised by the machine width `w`: each
    op carries one ported instruction (`JasminModel.JInstr w`). An op consumes
    one `machine w` (the incoming state) and produces one `machine w` (the
    outgoing state). -/
inductive X86Op (w : Nat) where
  /-- A single straight-line scalar/ADX instruction. -/
  | instr (i : JInstr w)

/-! ## 3. The dialect -/

/-- The x86 backend dialect: `Op` is the ported instruction set `X86Op w`,
    `Ty` is `X86Ty`. -/
@[reducible] def x86Dialect (w : Nat) : Dialect :=
  { Op := X86Op w, Ty := X86Ty }

/-! ## 4. Op signatures -/

/-- Every instruction op consumes one `machine w` and returns one `machine w`
    (the state-passing signature). -/
instance instSignature (w : Nat) : DialectSignature (x86Dialect w) where
  sig _ := [X86Ty.machine w]
  ret _ := X86Ty.machine w

/-! ## 5. Op denotation — the wiring to `evalInstr`

The denotation of `X86Op.instr i` on the single incoming state `s` is
`JasminModel.evalInstr s i`. This is the only place the dialect touches
semantics: it delegates to the faithful Jasmin transcription, op for op. -/

instance instDenote (w : Nat) : DialectDenote (x86Dialect w) where
  denote op := match op with
    | .instr i => fun args => evalInstr (args.head : JState w) i

/-! ## 6. Lowering a straight-line block to a `Com`

`lowerBlock` takes a `List (JInstr w)` and builds a
`Com (x86Dialect w) [machine w] (machine w)`: each instruction becomes a
`.var` binding an `X86Op.instr` applied to the most-recent state variable
(`.here`), and the continuation runs with the new state at the head of the
context. The empty block returns the input state. This mirrors the
`Com`-building shape of `ComToVeir_JasminDialect`'s smoke programs, threading
the machine state through the De Bruijn context. -/

/-- A one-instruction `Expr`: apply `X86Op.instr i` to the most-recently-bound
    state variable (`.here`) in a context whose head is `machine w`. -/
def instrExpr {w : Nat} (Γ : Ctxt (x86Dialect w)) (i : JInstr w) :
    Expr (x86Dialect w) (X86Ty.machine w :: Γ) (X86Ty.machine w) :=
  { op := X86Op.instr i
    retTy_eq := rfl
    args := .cons (Ctxt.Var.here) .nil }

/-- Lower a straight-line block to a `Com` that threads the head state variable
    through one `X86Op.instr` per instruction. The context grows by one
    `machine w` per instruction; the result returns the final state. -/
def lowerBlock {w : Nat} :
    {Γ : Ctxt (x86Dialect w)} → List (JInstr w) →
      Com (x86Dialect w) (X86Ty.machine w :: Γ) (X86Ty.machine w)
  | _, [] => .ret Ctxt.Var.here
  | Γ, i :: is => .var (instrExpr Γ i) (lowerBlock (Γ := X86Ty.machine w :: Γ) is)

/-! ## 7. Lowering-correctness theorem

`lowerBlock_denote` proves the denotation of the lowered `Com` equals
`JasminModel.runBlock` on the source block, for **all** straight-line blocks and
**all** incoming states. The proof is by induction on the block, peeling one
`evalInstr` per step; the `Expr.denote`/`Com.denote` of an `instrExpr` reduces
to `evalInstr` on the head state by the `denote_instr` wiring. -/

/-- The denotation of the lowered block, evaluated on a valuation whose head is
    the incoming state `s`, equals `runBlock s` on the source block. The
    valuation tail is irrelevant (the chain only reads the most-recent state). -/
theorem lowerBlock_denote {w : Nat} {Γ : Ctxt (x86Dialect w)}
    (block : List (JInstr w)) (s : JState w) (V : Ctxt.Valuation Γ) :
    (lowerBlock (Γ := Γ) block).denote (.cons s V) = runBlock s block := by
  induction block generalizing Γ s V with
  | nil => rfl
  | cons i is ih =>
      show (lowerBlock (Γ := X86Ty.machine w :: Γ) is).denote
            ((Ctxt.Valuation.extend (.cons s V) ((instrExpr Γ i).denote (.cons s V))))
          = runBlock s (i :: is)
      have hstep : (instrExpr Γ i).denote (.cons s V) = evalInstr s i := rfl
      rw [hstep]
      simpa using! ih (Γ := X86Ty.machine w :: Γ) (s := evalInstr s i)
        (V := .cons s V)

/-- The closed-block specialisation: on a singleton context `[machine w]`, the
    lowered block's denotation on `⟨s⟩` is `runBlock s block`. This is the
    state-transformer reading of the dialect: `lowerBlock block` denotes the
    function `s ↦ runBlock s block`. -/
theorem lowerBlock_denote_closed {w : Nat} (block : List (JInstr w))
    (s : JState w) :
    (lowerBlock (Γ := []) block).denote (.cons s .nil) = runBlock s block :=
  lowerBlock_denote block s .nil

/-! ## 8. The concrete payoff: the real emitted `#MULX → #ADCX → #ADOX` block

The straight-line carry-chain idiom from the emitted kernel
`bench/mpn_adxblk_carry_compare/mpn_addmul_1_adx_blk4_64.jazz` (lines 17–19):

```
hi0, lo0 = #MULX(b, t0);     // full product
cf,  r0  = #ADCX(r0, lo0, cf); // accumulate low word into the CF chain
of,  r0  = #ADOX(r0, cy, of);  // accumulate carry word into the OF chain
```

`TranslationValidation.lean` (the `Jasmin` namespace) validates this block's
`evalInstr`/`runBlock` machine-state transform against Jasmin's compiled Rocq
sequence evaluation. Here we lower the same block to `Com (x86Dialect 64)` and
prove the lowered-and-denoted state equals `runBlock` — i.e. the lowering is
denotation-preserving on the rocq-validated block. The pin at the end asserts
the resulting words and flags match the Jasmin output (`lo0 = 2^64-3`,
`hi0 = 2`; CF set after ADCX, OF clear after ADOX, `r0 = 107`). -/

/-- The emitted block as a `List (JInstr 64)`. -/
def mulxAdcxAdoxBlock : List (JInstr 64) :=
  [ .mulx "hi0" "lo0" (.reg "b") (.reg "t0")
  , .adcx "r0" (.reg "lo0")
  , .adox "r0" (.reg "cy") ]

/-- The initial machine state from the validated example: `b = 2^64-1`,
    `t0 = 3`, `r0 = 10`, `cy = 100`, `CF = OF = some false`. -/
def mulxAdcxAdoxInit : JState 64 :=
  { regs := fun r => if r = "b" then BitVec.allOnes 64
                     else if r = "t0" then 3
                     else if r = "r0" then 10
                     else if r = "cy" then 100 else 0
    flags := { cf := some false, of := some false } }

/-- **Lowering correctness on the real emitted block.** Lowering the
    `#MULX → #ADCX → #ADOX` carry-chain block to `Com (x86Dialect 64)` and
    denoting it on the initial state yields exactly `runBlock` on the source
    block — the same machine-state transform validated against Jasmin's
    compiled Rocq model in `TranslationValidation.lean`. -/
theorem mulxAdcxAdox_lowering_correct :
    (lowerBlock (Γ := []) mulxAdcxAdoxBlock).denote (.cons mulxAdcxAdoxInit .nil)
      = runBlock mulxAdcxAdoxInit mulxAdcxAdoxBlock :=
  lowerBlock_denote_closed mulxAdcxAdoxBlock mulxAdcxAdoxInit

/-- The denoted machine state matches the rocq-validated Jasmin output: after
    lowering and denoting the block, `r0 = 107`, `CF = some true`,
    `OF = some false` (the values pinned in `TranslationValidation.lean`'s
    `runBlock` example for the same block). -/
theorem mulxAdcxAdox_lowering_matches_jasmin :
    let s := (lowerBlock (Γ := []) mulxAdcxAdoxBlock).denote (.cons mulxAdcxAdoxInit .nil)
    (s.get "r0").toNat = 107 ∧ s.flags.cf = some true ∧ s.flags.of = some false := by
  rw [mulxAdcxAdox_lowering_correct]
  native_decide

/-! ## 9. Smoke test: a two-instruction block as a `Com`

A minimal sanity check that the dialect/`Com`/lowering plumbing computes:
`mov a, 5; add a, 8` on the zero state leaves `a = 13`. -/

/-- `mov a, 5; add a, 8` lowered and denoted on the zero state: `a = 13`. -/
example :
    let s0 : JState 64 := { regs := fun _ => 0 }
    let block : List (JInstr 64) := [.mov "a" (.imm 5), .add "a" (.imm 8)]
    (((lowerBlock (Γ := []) block).denote (.cons s0 .nil)).get "a").toNat = 13 := by
  intro s0 block
  rw [lowerBlock_denote_closed block s0]
  native_decide

/-! ## 10. General lowering — outside this module's scope

`lowerBlock` covers the straight-line scalar+ADX subset: a `List (JInstr w)`
threaded through the single `machine w` value. Two control-flow cases reduce to
it: `LoopUnroll.lean` (bounded counter loops, by unrolling) and `Cond.lean`
(forward conditionals on a **public** condition, by branch selection). The
**general** lowering from jasmin's `Linear.lprog` with *unstructured* CFG
(backward jumps / arbitrary labels) and calls into a multi-block `Com` — i.e.
extending `x86Dialect` with region-carrying control-flow ops (the analogue of
lean-mlir's `Com` regions) and proving preservation across blocks — is not
modeled here; no declaration in this module assumes it. -/

end CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
