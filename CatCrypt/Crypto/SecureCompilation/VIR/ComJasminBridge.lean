/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.WholeFnLowering
import CatCrypt.Crypto.SecureCompilation.VIR.ExecAdequacy

/-!
# The keystone semantic bridge: the compiler's `Com` denotation and the
# reference Jasmin operational semantics agree on emitted arithmetic

The compiler carries **two** semantic frameworks for the lowered Jasmin code,
and this file states — sorry-free — the cleanest TRUE connection between them.

## The executor relationship (the central finding)

There are two distinct executors, running over two distinct ASTs and two
distinct state representations. They are **genuinely separate frameworks**, not
the same executor:

| | JasminPrint side | psem.v mirror side |
|---|---|---|
| executor | `JasminPrintSemCorrect.runProg` / `execCom` | `CoqSemMirror.execCmd` / `execInstrR` |
| AST run | `JasminAST.InstrR` (`JasminAST.lean:258`) | `CoqSemMirror.InstrR` (`JasminCoqSemMirror.lean:436`) |
| state | `Store = String → DynVal` (`⟦reg w⟧ = BitVec w`) | `Estate` (memory + byte-encoded `Vmap`, `Value`) |
| value world | typed words (`BitVec w`) | `Value` (`.Vint`, `.Vword`, byte arrays) |
| top result | `runProg = Com.denote` (`WholeFnLowering.lowerComToProg_sem_eq'`) | `execInstrR … = .ok s' → SemIr …` (`ExecAdequacy.execInstrR_sound`) + completeness |
| reference | — (the *new* word-level evaluator) | the line-by-line port of jasminc's Coq `psem.v` relation |

**Crucially: the two `InstrR` types are different inductives.** `LowCT` /
`JasminPrint` / `WholeFnLowering` use `CatCrypt.Crypto.Jasmin.InstrR`
(`= JasminAST.InstrR`); the `SemIr` / `execCmd` adequacy uses
`CatCrypt.Crypto.Jasmin.CoqSemMirror.InstrR`. `JasminCoqSemMirror.lean` does not
import `JasminAST` at all. The structural differences are catalogued in
`InstrRReflect.lean` §9 (asm-op carrier `AsmOp` vs `String`, `Var.vtype`
`SType` vs `Atype`, `GVar.gs` `Bool` vs `VScope`, …). A translation between them
exists **only as an unverified `MetaM` reifier** (`reifyInstrRMirror%`), with no
denotation-preservation lemma.

So the relationship is option **(c)** of the scoping task: the frameworks are
separate, and the honest bridge is that **both characterise `Com.denote`** on
emitted code. The JasminPrint side does so *definitionally* (`runProg` is proved
equal to `Com.denote`). The psem side does so up to:

1. the syntactic `JasminAST.InstrR → CoqSemMirror.InstrR` translation (the
   mechanical-but-unverified reifier), and
2. the `Store ↔ Estate` byte-encoding round-trip (`DynVal` words ↔ `Value` byte
   arrays) — the *same* deferred "byte-layout encoding" piece flagged in
   `JasminPrintSemCorrect.lean:36` and `LatticeToJasminDenote.lean`.

What does cross the gap cleanly, and is proved here, is the **arithmetic
content**: the integer add the psem `OpSem` performs and the `BitVec` add that
`Com.denote`'s `regArith .add` performs are the *same operation on the same
numerals*. That is the load-bearing fact a byte-encoding bijection would lift to
a full state correspondence; we prove it directly, with no `sorry`.

## What is proved here (all sorry-free)

* `denote_add_smoke` / `smoke_run_eq_denote` — the JasminPrint executor on the
  golden-path two-op kernel `JasminDialect.smokeProg` equals `Com.denote`
  (re-exported from `WholeFnLowering`; the JasminPrint half of the bridge).
* `psem_add_eq_int_add` — the reference `psem.v` `OpSem` add (`addOpSem`) on two
  integer values computes the mathematical `Int` sum: `.Vint a + .Vint b ↦
  .Vint (a + b)`.
* `denote_add_int_agree` — the **value-level correspondence**: on numerals `a b`
  that fit the word width, the psem integer add (`a + b : Int`) and the
  `Com.denote`-level `regArith .add` (`a + b : BitVec w`) carry the same value,
  i.e. `((a + b : Int)).toNat'-into-BitVec = (a : BitVec w) + (b : BitVec w)`
  for representable inputs. (Stated and proved on the concrete golden-path
  witness `5, 1` and generically for representable numerals.)
* `golden_add_bridge` — the **keystone**: on the golden-path add witness, *both*
  frameworks agree. The psem side: the executor run of the emitted `Cassgn`
  `x := y + 1` from `y = 5` *witnesses* the reference relational step `SemIr`
  and lands `x = 6` (from `ExecAdequacy`). The JasminPrint / `Com.denote` side:
  `regArith .add 5 1 = 6` over `BitVec`. Same arithmetic, same numeral, the two
  reference semantics coincide on this emitted operation.
* `golden_bridge_summary` — packages the two coincidences (JasminPrint =
  `Com.denote`; psem `SemIr` witnessed with the matching value) into one
  statement: the compiler's IR denotation and the reference operational
  semantics agree on the golden-path emitted arithmetic.

## Honest scope / the precise gap

This bridge is **value-level and worked-example-concrete on the add kernel**, not
a generic `∀ com, SemIr-of-(translate (lower com)) ↔ Com.denote com`. The two
missing pieces for the generic statement are exactly (1) a *verified* AST
translation `JasminAST.InstrR → CoqSemMirror.InstrR` (currently only the
unverified reifier) and (2) the `Store ↔ Estate` byte-encoding bijection. Both
are catalogued above and pre-existing deferrals; neither is introduced as a
`sorry` here. The JasminPrint half is fully generic (any straight-line `Com`);
the psem half is the worked golden-path witness plus the value-level arithmetic
correspondence that any encoding bijection would lift.

0 sorries.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridge

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.Jasmin.CoqSemMirror

/-! ## 1. The JasminPrint half — `runProg = Com.denote` on the golden-path kernel

This half is fully generic over straight-line `Com`s; the golden-path two-op
`smokeProg` is the concrete witness. We re-export the proven results so the
bridge file is self-contained on the example. -/

/-- The golden-path kernel `smokeProg` denotes (in the compiler's `Com` IR
    semantics) to `(a + b).zeroExtend 64` — the `regArith .add` then `castW`. On
    the bridge witness `5, 1` this is `(6 : BitVec 32).zeroExtend 64`. -/
theorem denote_add_smoke :
    JasminDialect.smokeProg.denote
        (.cons (5 : BitVec 32) (.cons (1 : BitVec 32) .nil))
      = ((6 : BitVec 32).zeroExtend 64) := by
  rfl

/-- **JasminPrint half of the bridge.** Running the lowered golden-path kernel
    under the reference word-level evaluator equals its `Com.denote`, for any
    leaf semantics (vacuous here — no `extCall`). This is
    `WholeFnLowering.smokeProg_run_eq` re-stated; the JasminPrint executor is, by
    construction, the `Com` denotation on this fragment. -/
theorem smoke_run_eq_denote {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (V : Ctxt.Valuation (d := jasminDialect) [JasminTy.reg 32, JasminTy.reg 32]) :
    runProg leafSem JasminDialect.smokeProg V
      = JasminDialect.smokeProg.denote V :=
  WholeFnLowering.smokeProg_run_eq hLeaf V

/-! ## 2. The psem.v half — the reference `OpSem` add is the mathematical add

The reference operational semantics evaluates `regArith .add`-flavoured
arithmetic through an `OpSem.sem_sop2` (here `ExecAdequacy.WorkedExample`'s
`addOpSem`, covering `Oadd Op_int`). We record that this reference add is the
mathematical `Int` add — the fact a byte-encoding bijection lifts to the word
add of `Com.denote`. -/

open ExecAdequacy.WorkedExample
open OpSemCoverage.AssignExample

/-- **The reference `psem.v` `OpSem` add is mathematical integer addition.** The
    golden-path `addOpSem.sem_sop2 (Oadd Op_int) (.Vint a) (.Vint b)` returns
    exactly `.Vint (a + b)`. This is the reference-semantics side of the
    arithmetic the compiler emits for `regArith .add`. -/
theorem psem_add_eq_int_add (a b : Int) :
    addOpSem.sem_sop2 (.Oadd .Op_int) (.Vint a) (.Vint b)
      = .ok (.Vint (a + b)) := rfl

/-! ## 3. The value-level correspondence — the two adds agree on representable
numerals

`Com.denote`'s `regArith .add` is `BitVec` add (`JasminBinOp.apply .add a b =
a + b`); the psem side's add is `Int` add. They carry the *same* value on inputs
that fit the word: the `BitVec w` of `(a + b : Int)` equals
`(a : BitVec w) + (b : BitVec w)` when `a + b < 2^w`. We state this generically
and pin the golden-path witness `5, 1, w = 32`. -/

/-- **Value-level add correspondence.** Pushing the integer sum `a + b` into
    `BitVec w` equals the `BitVec` add of the pushed operands: the psem integer
    add and the `Com.denote` `BitVec` add (`regArith .add`) carry the same value.
    This holds unconditionally — `BitVec.ofNat` already reduces mod `2 ^ w`,
    which *is* the `BitVec` add's wraparound. The no-overflow side-condition
    `_h : a + b < 2 ^ w` records the regime in which this correspondence is
    *faithful* (no wraparound), i.e. the regime a `Store ↔ Estate` byte-encoding
    bijection would establish; it is recorded, not needed for the equation. This
    is the arithmetic core that such a bijection lifts to a full state
    correspondence. -/
theorem denote_add_int_agree (w : Nat) (a b : Nat) (_h : a + b < 2 ^ w) :
    (BitVec.ofNat w (a + b))
      = (BitVec.ofNat w a) + (BitVec.ofNat w b) := by
  rw [BitVec.ofNat_add]

/-- **Golden-path witness of the value-level correspondence.** The psem add
    `5 + 1 = 6 : Int` and the `Com.denote` `regArith .add` `5 + 1 = 6 : BitVec
    32` carry the same numeral. Combines `JasminBinOp.apply .add` (the denote
    op) with `denote_add_int_agree`. -/
theorem golden_add_value_agree :
    JasminBinOp.apply .add (w := 32) (5 : BitVec 32) (1 : BitVec 32)
      = BitVec.ofNat 32 (((5 : Int) + 1).toNat) := by
  decide

/-! ## 4. The keystone bridge — both frameworks agree on the emitted add

On the golden-path add operation `x := y + 1` (`y = 5`):

* **psem.v / reference side.** The emitted `Cassgn` *run* witnesses the relational
  step `SemIr.Eassgn` and lands `x = 6` (`ExecAdequacy.assignXY_run_witnesses_SemIr`).
* **`Com.denote` / JasminPrint side.** `regArith .add 5 1 = 6` over `BitVec`
  (`denote_add_smoke` carries it through `castW`).

The two reference semantics — the compiler's `Com` denotation and the jasminc
`psem.v` mirror — coincide on this emitted operation: same op, same numerals,
same result `6`. -/

/-- **Keystone bridge (golden-path add).** Both semantic frameworks agree on the
    emitted golden-path addition:

    * the reference `psem.v` run of the emitted `Cassgn` `x := y + 1` from
      `y = 5` *witnesses* the relational step `SemIr` **and** computes `x = 6`;
    * the compiler's `Com.denote` of `regArith .add` on `5, 1` is `6`
      (`BitVec 32`), and the value-level correspondence shows this is the *same*
      `6` the psem integer add produces.

    This is the cleanest TRUE connection: the two reference semantics for the
    compiler's emitted code coincide on the golden-path arithmetic. -/
theorem golden_add_bridge :
    -- psem.v / reference relational side: the run witnesses `SemIr` and lands x = 6
    (SemIr (Mem := OpSemCoverage.AssignExample.TrivialMem) addAsmSem addOpSem []
        Prog.empty (startState 5) assignXY assignXY_post
      ∧ readX assignXY_post = some 6)
    -- Com.denote / JasminPrint side: regArith .add 5 1 = 6 over BitVec
    ∧ JasminBinOp.apply .add (w := 32) (5 : BitVec 32) (1 : BitVec 32)
        = (6 : BitVec 32)
    -- and the two `6`s are the same value (value-level correspondence)
    ∧ ((6 : BitVec 32) = BitVec.ofNat 32 (((5 : Int) + 1).toNat)) := by
  refine ⟨assignXY_run_witnesses_SemIr, ?_, ?_⟩
  · decide
  · decide

/-- **Bridge summary.** Packages the two halves: on the golden-path kernel the
    JasminPrint executor equals `Com.denote` (generic, for any leaf semantics),
    and on the golden-path add the reference `psem.v` semantics witnesses the
    matching value. Together: the compiler's `Com` IR denotation and the
    reference Jasmin operational semantics agree on the emitted arithmetic. -/
theorem golden_bridge_summary {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (V : Ctxt.Valuation (d := jasminDialect) [JasminTy.reg 32, JasminTy.reg 32]) :
    -- JasminPrint executor = Com.denote (the IR-semantics half, generic in V)
    (runProg leafSem JasminDialect.smokeProg V = JasminDialect.smokeProg.denote V)
    -- psem.v reference relational step witnessed, with the matching value
    ∧ (SemIr (Mem := OpSemCoverage.AssignExample.TrivialMem) addAsmSem addOpSem []
        Prog.empty (startState 5) assignXY assignXY_post
       ∧ readX assignXY_post = some 6) :=
  ⟨smoke_run_eq_denote hLeaf V, assignXY_run_witnesses_SemIr⟩

end CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridge
