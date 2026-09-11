/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow

/-!
# Loop-over-call orchestration front (combinator core)

`OrchestrationFront.buildOrchCom` sources the *straight-line* call band (a
sequence of `.extCall`-over-`stackArr` leaves lowered by the array-ABI backend).
It has **no loop node**: the whole-prover orchestration LOOPS — the per-iteration
`call <leaf>` + pointer-stride that route a field leaf over a strided operand
schedule — are emitted one level lower, as an owned-backend
`X86Backend.LprogControlFlow.loopLcmd` wrapping a body `Lcmd`.

This module is the **upstream combinator core** for the *loop-over-call* shape.
It imports only `JasminLprogExport` + `LprogControlFlow` — the shared owned
backend — and NOTHING from the whole-prover emit modules, so it sits upstream of
them with no import cycle. The whole-prover drivers

* `Plonky3OrchLoopsEmit.orchLoopFundef`  — single-leaf-call strided loop,
* `ZkSumCheckWholeProverEmit.sumcheckLoopFundef` — two-leaf-call round loop
  with callee-saved base reload,
* `Plonky3ProveDriverEmit.proveDriverFundef` — straight-line phase call
  sequence (no loop),

set their DEPLOYED `Lfundef` `:= buildOrchLoop <spec>` (resp.
`buildOrchCallSeq …`): the deployed kernel IS this front's output, so the driver
body is produced from a schedule (`bandLcmd`) wrapped by the verified `loopLcmd`
back-edge, not a hand-typed `Lcmd` literal.

The step language (`OrchStep`/`stepToLinstr`/`bandLcmd`), the loop spec
(`OrchLoopSpec`), the two combinators (`buildOrchLoop`/`buildOrchCallSeq`), and
the two whole-prover loop specs (`strideCallSpec`/`sumcheckSpec`) live here. The
*validation* lemmas — that each deployed driver equals its `buildOrchLoop`
output — live in the downstream `OrchLoopFront`, which imports both this module
and the emit modules.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.OrchFront

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow
  (loopLcmd loopLcmd_length)

/-! ## 1. The loop-body step language

An orchestration loop body is a short schedule of four instruction shapes: a void
near-`call` to a field leaf, register-to-register moves (base-pointer reload /
seed), and immediate `ADD`/`SUB` on a pointer or counter register. `OrchStep`
names them symbolically; `stepToLinstr` renders each to the owned-backend
`Linstr`. All widths flow through `withWidthTag`, so a 64-bit step carries the
`":64"` tag the renderer needs. -/

/-- One step of an orchestration-loop schedule. -/
inductive OrchStep where
  /-- A void near-`call` to a field-leaf symbol: `LinstrR.Lcall none (leaf, 0)`
      ⇒ `call leaf` (the intra-object sibling call). -/
  | call (leaf : String)
  /-- A register-to-register move `MOV dst, src` (base-pointer reload / seed). -/
  | movRR (dst src : String)
  /-- An immediate move `MOV dst, #imm` (counter / index initialisation). -/
  | movImm (dst : String) (imm : Nat)
  /-- An immediate add `ADD reg, #imm` (pointer stride advance). -/
  | addImm (reg : String) (imm : Nat)
  /-- An immediate subtract `SUB reg, #imm` (counter decrement). -/
  | subImm (reg : String) (imm : Nat)
  deriving DecidableEq, Repr

/-- Render one `OrchStep` to an owned-backend `Linstr` at counter/op width `w`.
    The `Lopn` mnemonics carry `withWidthTag w`, matching the width tag every
    hand-authored orchestration body writes (`"ADD:64"`, `"SUB:64"`, `"MOV:64"`). -/
def stepToLinstr (w : Nat) : OrchStep → Linstr
  | .call leaf   => ⟨0, .Lcall none (leaf, 0)⟩
  | .movRR d s   => ⟨0, .Lopn [.reg d] (withWidthTag w "MOV") [.reg s]⟩
  | .movImm d v  => ⟨0, .Lopn [.reg d] (withWidthTag w "MOV") [.imm v]⟩
  | .addImm r v  => ⟨0, .Lopn [.reg r] (withWidthTag w "ADD") [.reg r, .imm v]⟩
  | .subImm r v  => ⟨0, .Lopn [.reg r] (withWidthTag w "SUB") [.reg r, .imm v]⟩

/-- Render a step schedule to an `Lcmd` (the body / prologue band). -/
def bandLcmd (w : Nat) (steps : List OrchStep) : Lcmd := steps.map (stepToLinstr w)

/-! ## 2. The loop spec + the `buildOrchLoop` front -/

/-- A loop-over-call orchestration spec: the counter width `w`, the back-edge top
    label `top`, the counter register `counter`, a `prologue` step schedule
    (counter init / base seed, emitted once before the loop), a per-iteration
    `body` step schedule (the leaf `call` + pointer/counter arithmetic), and the
    SysV argument ABI (`tyin` widths, `argRegs` names). Defaults are the common
    whole-prover case: 64-bit, top label `0`, counter `%r8`, `(%rdi,%rsi)` ABI. -/
structure OrchLoopSpec where
  /-- Counter / op width (64 for a U64 loop). -/
  w : Nat := 64
  /-- Back-edge top label (distinct per loop in one function). -/
  top : LLabel := 0
  /-- Loop counter register (public trip count). -/
  counter : String := "R8"
  /-- One-shot prologue schedule (counter init / base seed). -/
  prologue : List OrchStep := []
  /-- Per-iteration body schedule (leaf call + pointer/counter arithmetic). -/
  body : List OrchStep := []
  /-- SysV argument register widths. -/
  tyin : List Nat := [64, 64]
  /-- SysV argument register names. -/
  argRegs : List String := ["RDI", "RSI"]

/-- **The loop-over-call orchestration front.** From a loop spec, generate the
    driver `Lfundef`: the prologue band, then the body band wrapped once in the
    verified `loopLcmd` back-edge. The body is produced from the step schedule
    (`bandLcmd`), not hand-authored, and the loop wrapper is `loopLcmd` — so the
    driver's control flow is the owned back-edge whose shape/size
    `LprogControlFlow` pins, and its provenance is the front, not a raw `Lcmd`
    literal. -/
def buildOrchLoop (spec : OrchLoopSpec) : Lfundef :=
  { lfd_tyin := spec.tyin, lfd_arg := spec.argRegs
    lfd_body := bandLcmd spec.w spec.prologue
                  ++ loopLcmd spec.w spec.top spec.counter (bandLcmd spec.w spec.body)
    lfd_tyout := [], lfd_res := [] }

/-- The sibling for the degenerate **no-loop** case: a straight-line call/step
    sequence with no back-edge (the phase-driver `plonky3_prove`). Body is the
    rendered schedule, no `loopLcmd`. -/
def buildOrchCallSeq (w : Nat) (steps : List OrchStep)
    (tyin : List Nat := [64, 64]) (argRegs : List String := ["RDI", "RSI"]) : Lfundef :=
  { lfd_tyin := tyin, lfd_arg := argRegs
    lfd_body := bandLcmd w steps
    lfd_tyout := [], lfd_res := [] }

/-! ## 3. Generation gate + shape facts

`buildOrchLoop` is total, so the analogue of `OrchestrationFront`'s
`… |>.isSome = true` gate is a decidable well-formedness `Bool`: the body ends
with the counter decrement `SUB counter, #1` and contains at least one leaf
`call`. A `some`-shaped schedule is exactly `wellFormed spec = true` (a `decide`
/`rfl`). -/

/-- A body schedule is well-formed for the loop-over-call band iff it contains a
    leaf `call` and its last step decrements the loop counter. -/
def OrchLoopSpec.wellFormed (spec : OrchLoopSpec) : Bool :=
  spec.body.any (fun s => match s with | .call _ => true | _ => false)
    && (spec.body.getLast? == some (.subImm spec.counter 1))

/-- The loop body length is constant in the trip count: the schedule length plus
    the three control instrs (`loopLcmd`'s label + compare + back-edge). -/
theorem buildOrchLoop_body_length (spec : OrchLoopSpec) :
    (buildOrchLoop spec).lfd_body.length
      = spec.prologue.length + (spec.body.length + 3) := by
  simp [buildOrchLoop, bandLcmd, loopLcmd_length, List.length_append]

/-! ## 4. The two whole-prover loop specs

These are pure `OrchLoopSpec` values — no dependency on the emit modules — so
they live here, upstream of the drivers they source. The downstream
`OrchLoopFront` validates that each deployed driver equals `buildOrchLoop` of its
spec (a `rfl`, since the deployed `Lfundef` IS this front's output). -/

/-- The module-1 spec: a single-leaf-call strided loop
    (`call leaf ; ADD rdi,#so ; ADD rsi,#si ; SUB r8,#1`), counter init prologue.
    Sources `Plonky3OrchLoopsEmit.orchLoopFundef`. -/
def strideCallSpec (leaf : String) (n so si : Nat) : OrchLoopSpec :=
  { prologue := [.movImm "R8" n]
    body := [.call leaf, .addImm "RDI" so, .addImm "RSI" si, .subImm "R8" 1] }

/-- The module-2 spec: a two-leaf-call sum-check round loop with callee-saved
    base pointers `%r12`/`%r13` reloaded into `%rdi`/`%rsi` before each call and
    advanced at the tail. Sources
    `ZkSumCheckWholeProverEmit.sumcheckLoopFundef`. -/
def sumcheckSpec (n so si : Nat) : OrchLoopSpec :=
  { prologue := [.movRR "R12" "RDI", .movRR "R13" "RSI", .movImm "R8" n]
    body :=
      [ .movRR "RDI" "R12", .movRR "RSI" "R13", .call "zk_sumcheck_round_step_rc"
      , .movRR "RDI" "R12", .movRR "RSI" "R13", .call "zk_poseidon2_squeeze_rc"
      , .addImm "R12" so, .addImm "R13" si, .subImm "R8" 1 ] }

/-- The module-1 spec is well-formed (generation gate). -/
theorem strideCallSpec_wellFormed (leaf : String) (n so si : Nat) :
    (strideCallSpec leaf n so si).wellFormed = true := rfl

/-- The module-2 spec is well-formed (generation gate). -/
theorem sumcheckSpec_wellFormed (n so si : Nat) :
    (sumcheckSpec n so si).wellFormed = true := rfl

end CatCrypt.Crypto.SecureCompilation.Dialects.OrchFront
