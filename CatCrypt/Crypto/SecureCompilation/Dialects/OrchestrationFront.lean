/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-!
# Orchestration front: a phase-schedule → `Com` combinator for the call band

The EC/pairing and whole-prover-spine owned-emit modules
(`Pairing.Bls12_377Emit`, `Pairing.EcPairingOwnedEmit`, the plonky3 spines, …)
express a whole-protocol orchestration — the gather/`call`/scatter glue over
opaque `.stackArr` leaves — as a straight-line `Com jasminDialect` whose every
binding is an opaque `.extCall` over point/field buffers. That `Com` is then
lowered to owned x86 by the array-ABI backend
(`VIR.JasminLprogExport.Com.toLprogArrAbi`, in `ArrAbiOrch`).

Those orchestration `Com`s are currently **hand-authored** with explicit
de-Bruijn operand chains — e.g. `Bls12_377Emit.pairingProductCom` threads
`.here` / `.there (.there (.there .here))` by hand across three leaf calls, and a
matching `pairingProductCom_denote` is written for each. A miscounted `.there`
silently references the wrong buffer. This is the same fragility
`SecureCompilation.ComBuilder` removed for the scalar (`.reg 64`) straight-line
field kernels, but that builder is monomorphic — every binding and operand is a
`.reg 64` — so it cannot express the **heterogeneous** array-ABI orchestration
(a `bls377_pairing` leaf takes a `G1` (96 B) and a `G2` (192 B) buffer and
returns a `GT` (576 B) buffer; a `bls377_Fp12_mul` takes two `GT`s).

This module is the heterogeneous sibling: a front combinator `buildOrchCom` that
takes a **phase schedule** — a sequence of leaf calls, each naming its leaf
symbol, its argument/result `.stackArr` types, and the **root-order slots** of
its operand buffers — and generates the marshalled orchestration
`Com jasminDialect`, resolving every de-Bruijn operand chain automatically. The
generated `Com` feeds `Com.toLprogArrAbi` unchanged: the front now SOURCES the
orchestration instead of hand-authoring it.

## Slot convention (matches `ArrAbiOrch.exprArgSlots`)

A **root-order slot** counts bindings from the oldest (the tail of the context):
the argument buffers occupy slots `0 … nArgs-1` (slot `0` is the last element of
the initial context `Γ₀`, i.e. its tail), and the `k`-th leaf call's result
takes slot `nArgs + k`. In a context `Γ` of length `|Γ|`, root slot `s` sits at
de-Bruijn index `|Γ| - 1 - s` (`.there^(|Γ|-1-s) .here`) — exactly the inverse of
`ArrAbiOrch.exprArgSlots`' `curDepth - 1 - varIndex v`, so a schedule's slots and
the array-ABI backend's frame layout agree by construction.

## What it covers vs. not

It covers any **straight-line `extCall`-over-`stackArr` orchestration**: a
sequence of by-pointer leaf calls whose operands are argument buffers or the
results of earlier calls, returning one buffer — the EC/pairing verifier
equations, MSM-term accumulators, pairing-product checks, and whole-prover call
spines. It does **not** introduce control flow (`while`/branch/loop leaves stay
the loop-node combinators' job) and it does not itself emit — lowering is
`Com.toLprogArrAbi`'s job, whose backend memory-safety framing
(`comToLfundefArrAbi_memSafe`) carries over verbatim to any `Com` this front
produces.

`buildOrchCom` is total and structurally recursive on the schedule; it returns
`none` on an ill-formed schedule (an out-of-range slot, a slot whose buffer type
does not match the declared operand type, or a returned slot of the wrong type),
so a well-typed orchestration is exactly a `some`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.OrchestrationFront

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. The phase schedule -/

/-- One leaf call in an orchestration schedule: the opaque leaf symbol, its
    argument buffer types (in argument order), its result buffer type, and the
    **root-order slots** of its operand buffers (an argument buffer if
    `< nArgs`, an earlier call's result if `≥ nArgs`). -/
structure CallPhase where
  /-- The opaque leaf symbol (`bls377_pairing`, `g1_add`, `bls377_Fp12_mul`, …). -/
  leaf : String
  /-- The argument buffer types, in argument order. -/
  argTys : List JasminTy
  /-- The result buffer type (this binding's scratch). -/
  retTy : JasminTy
  /-- The root-order slots of the operand buffers, in argument order. -/
  argSlots : List Nat

/-! ## 2. `mkVarDB` / `mkVarSlot`: resolve a dependent `Ctxt.Var` from a slot

The heterogeneous analogue of `ComBuilder.mkVar`/`levelVar`: `ComBuilder.mkVar`
fixes the target type to `.reg 64` (so `.here` typechecks against a matched head),
but an orchestration operand can be any `.stackArr` width/size, so `mkVarDB` takes
the target type `τ` and checks the binding at the given de-Bruijn index has that
type, transporting `.here` along the decided equality. The transport reduces
through `Var.lookup` / `varIndex` by the kernel's definitional proof
irrelevance, so both the denotation and the array-ABI shape of a generated `Com`
compute exactly as for a hand-authored one. -/

/-- Build `Ctxt.Var Γ τ` from a de-Bruijn index `i` by recursion on the context.
    `none` if `i` is out of range, or if the binding at `i` does not have type
    `τ`. Resolves the `.there^i .here` chain the caller would otherwise
    hand-author. -/
def mkVarDB : (Γ : Ctxt jasminDialect) → (i : Nat) → (τ : JasminTy) →
    Option (Ctxt.Var Γ τ)
  | [], _, _ => none
  | t :: _, 0, τ => if h : t = τ then some (h ▸ Ctxt.Var.here) else none
  | _ :: Γ', (i + 1), τ => (mkVarDB Γ' i τ).map Ctxt.Var.there

/-- Resolve a **root-order slot** `s` (its stable, context-independent name) to a
    `Ctxt.Var` in a context `Γ`. Root slot `s` sits at de-Bruijn index
    `|Γ| - 1 - s` (the inverse of `ArrAbiOrch.exprArgSlots`). `none` if `s` is out
    of range or the buffer there is not of type `τ`. -/
def mkVarSlot (Γ : Ctxt jasminDialect) (s : Nat) (τ : JasminTy) :
    Option (Ctxt.Var Γ τ) :=
  if s < Γ.length then mkVarDB Γ (Γ.length - 1 - s) τ else none

/-! ## 3. `mkArgVars`: build the operand `HVector` from slots -/

/-- Build the typed operand `HVector` for a leaf call, against its argument-type
    signature `tys` and the operand root-slots `slots`. Each signature slot must
    resolve to a buffer of the matching type and the operand count must match. -/
def mkArgVars (Γ : Ctxt jasminDialect) :
    (tys : List JasminTy) → (slots : List Nat) →
    Option (HVector (fun ty => Ctxt.Var Γ ty) tys)
  | [], _ => some .nil
  | _ :: _, [] => none
  | ty :: tys, s :: ss =>
      match mkVarSlot Γ s ty, mkArgVars Γ tys ss with
      | some v, some rest => some (.cons v rest)
      | _, _ => none

/-! ## 4. `mkPhaseExpr`: the `extCall` `Expr` for one phase

The op is `.extCall p.leaf p.argTys p.retTy`; by the `DialectSignature`
instance its `sig` is `p.argTys` and its `ret` is `p.retTy`, so the operand
`HVector` from `mkArgVars` fits directly and `retTy_eq` is `rfl`. -/

/-- Build the opaque-leaf `Expr jasminDialect Γ p.retTy` for phase `p` — an
    `.extCall` over the operands resolved from `p.argSlots`. `none` when an
    operand does not resolve. -/
def mkPhaseExpr (Γ : Ctxt jasminDialect) (p : CallPhase) :
    Option (Expr jasminDialect Γ p.retTy) :=
  match mkArgVars Γ p.argTys p.argSlots with
  | some args =>
      some { op := .extCall p.leaf p.argTys p.retTy, retTy_eq := rfl, args := args }
  | none => none

/-! ## 5. `buildOrchCom`: the whole orchestration builder

Walk the phase schedule, emitting one `Com.var` per leaf call under a context
that grows on the left (`p.retTy :: Γ`), and close with `Com.ret` on the returned
slot. Structurally recursive on the schedule; the growing context threads the
de-Bruijn plumbing automatically. -/

/-- **The orchestration front.** From an initial argument context `Γ` (the input
    buffers), a phase schedule, the returned buffer's root slot, and the declared
    output type, generate the marshalled straight-line orchestration
    `Com jasminDialect Γ retTy`. `none` on any ill-typed / out-of-range slot. -/
def buildOrchCom :
    (Γ : Ctxt jasminDialect) → (sched : List CallPhase) → (retSlot : Nat) →
    (retTy : JasminTy) → Option (Com jasminDialect Γ retTy)
  | Γ, [], retSlot, retTy =>
      match mkVarSlot Γ retSlot retTy with
      | some v => some (.ret v)
      | none => none
  | Γ, p :: rest, retSlot, retTy =>
      match mkPhaseExpr Γ p with
      | none => none
      | some e =>
          match buildOrchCom (p.retTy :: Γ) rest retSlot retTy with
          | some body => some (.var e body)
          | none => none

/-! ## 6. Schedule well-formedness (the `some` characterisation)

A schedule that resolves is one whose every operand slot is in range with the
declared type and whose returned slot is in range with the declared output type.
`buildOrchCom … |>.isSome` is decidable, so a concrete schedule's well-formedness
is a `decide`. -/

/-- The final context a schedule builds over: each phase prepends its result type,
    so the context after the whole schedule is
    `(sched.map retTy).reverse ++ Γ₀`. -/
def ctxtAfter (Γ : Ctxt jasminDialect) (sched : List CallPhase) : Ctxt jasminDialect :=
  (sched.map CallPhase.retTy).reverse ++ Γ

/-- The final context is `Γ₀` when the schedule is empty. -/
@[simp] theorem ctxtAfter_nil (Γ : Ctxt jasminDialect) : ctxtAfter Γ [] = Γ := by
  simp [ctxtAfter]

/-- Prepending one phase extends the final context by that phase's result type at
    the newest end (the recursion `buildOrchCom` performs). -/
theorem ctxtAfter_cons (Γ : Ctxt jasminDialect) (p : CallPhase)
    (rest : List CallPhase) :
    ctxtAfter Γ (p :: rest) = ctxtAfter (p.retTy :: Γ) rest := by
  simp [ctxtAfter]

/-! ## 7. Word-move phases: interleaving `stackStore` / `stackLoad` / `regConst`

The `CallPhase` schedule above is whole-buffer SSA over `.extCall` only: every
binding is one opaque leaf call. A **sponge** needs finer granularity — it
scatters input words into the rate portion of a state buffer, calls the opaque
`permute` leaf, then gathers output words back out, with the word-moves
*interleaved* around the call. Those word-moves are exactly the Jasmin dialect's
own `stackStore` / `stackLoad` / `regConst` ops (see `JasminDialect`:
`stackStore w n : [stackArr w n, reg 64, reg w] → stackArr w n`,
`stackLoad w n : [stackArr w n, reg 64] → reg w`, `regConst w n : [] → reg w`),
which `JasminLprogExport` already lowers to interleaved `STOREIDX` / `LOADIDX`
word-moves around the `Lcall`.

This section extends the front **additively**: `CallPhase` and `buildOrchCom`
above are unchanged (the landed EC/pairing flips call them verbatim), and a
**phase sum** `OrchPhase` reuses `CallPhase` as its call case while adding the
three word-move cases. `buildOrchComP` walks a `List OrchPhase`, emitting the
matching `Com.var` per phase and closing with `Com.ret` — the same shape as
`buildOrchCom`, so an all-`call` schedule builds the *identical* `Com`
(`buildOrchComP_call_eq`). Every new phase threads a fresh result slot exactly
like the call phase, and each operand is resolved through the same `mkVarSlot`
root-slot convention, so a mixed call + word-move schedule and the array-ABI
backend's frame layout still agree by construction. -/

/-- One phase of a mixed orchestration schedule. The `call` case is a full
    `CallPhase` (an opaque `.extCall` leaf, unchanged from the call band); the
    three word-move cases name their operand buffers/words by **root-order slot**
    exactly like `CallPhase.argSlots`. Each phase binds a fresh result slot (its
    `retTy`), threading the de-Bruijn plumbing just as the call phase does. -/
inductive OrchPhase where
  /-- An opaque leaf call — the whole `CallPhase` band, reused verbatim. -/
  | call (p : CallPhase)
  /-- Scatter a word into a buffer: functional update
      `arr[idx] := val` via `stackStore w n`. `arrSlot` is the buffer being
      updated, `idxSlot` the index register (`reg 64`), `valSlot` the word
      (`reg w`). Binds the updated buffer (`stackArr w n`) at a fresh slot. -/
  | storeWord (w n : Nat) (arrSlot idxSlot valSlot : Nat)
  /-- Gather a word out of a buffer: `arr[idx]` via `stackLoad w n`. `arrSlot`
      is the source buffer, `idxSlot` the index register. Binds the loaded word
      (`reg w`) at a fresh slot. -/
  | loadWord (w n : Nat) (arrSlot idxSlot : Nat)
  /-- Materialise a compile-time constant word `imm : reg w` via `regConst w imm`
      (nullary — no operand slots). Used for zero-init / round constants / index
      immediates. Binds the constant (`reg w`) at a fresh slot. -/
  | setImm (w imm : Nat)

/-- The result type each phase binds (its fresh slot's type). Matches the op's
    `DialectSignature.ret`: `stackStore` returns the updated `stackArr w n`,
    `stackLoad` a `reg w` word, `regConst` a `reg w` constant. On `call` it is the
    underlying `CallPhase.retTy`, so `OrchPhase.retTy (.call p) = p.retTy`
    definitionally. -/
def OrchPhase.retTy : OrchPhase → JasminTy
  | .call p => p.retTy
  | .storeWord w n _ _ _ => .stackArr w n
  | .loadWord w _ _ _ => .reg w
  | .setImm w _ => .reg w

/-- Build the `Expr jasminDialect Γ p.retTy` for one phase `p`. The `call` case
    delegates to `mkPhaseExpr` unchanged; each word-move case resolves its operand
    slots through `mkVarSlot` (the same root-slot convention) and assembles the
    op's operand `HVector`. `retTy_eq` is `rfl` in every case because
    `OrchPhase.retTy` is defined to mirror `DialectSignature.ret`. `none` when an
    operand slot is out of range or mistyped. -/
def mkOrchExpr (Γ : Ctxt jasminDialect) :
    (p : OrchPhase) → Option (Expr jasminDialect Γ p.retTy)
  | .call p => mkPhaseExpr Γ p
  | .storeWord w n arrSlot idxSlot valSlot =>
      match mkVarSlot Γ arrSlot (.stackArr w n), mkVarSlot Γ idxSlot (.reg 64),
            mkVarSlot Γ valSlot (.reg w) with
      | some vArr, some vIdx, some vVal =>
          some { op := .stackStore w n, retTy_eq := rfl,
                 args := .cons vArr (.cons vIdx (.cons vVal .nil)) }
      | _, _, _ => none
  | .loadWord w n arrSlot idxSlot =>
      match mkVarSlot Γ arrSlot (.stackArr w n), mkVarSlot Γ idxSlot (.reg 64) with
      | some vArr, some vIdx =>
          some { op := .stackLoad w n, retTy_eq := rfl,
                 args := .cons vArr (.cons vIdx .nil) }
      | _, _ => none
  | .setImm w imm =>
      some { op := .regConst w imm, retTy_eq := rfl, args := .nil }

/-- **The extended orchestration front.** From an initial argument context `Γ`, a
    mixed schedule (`List OrchPhase` — leaf calls interleaved with word-moves), the
    returned buffer/word's root slot, and the declared output type, generate the
    marshalled straight-line `Com jasminDialect Γ retTy`. Identical recursion shape
    to `buildOrchCom`: emit one `Com.var` per phase over the left-growing context
    `p.retTy :: Γ`, close with `Com.ret`. `none` on any ill-typed / out-of-range
    slot, so a well-typed mixed schedule is exactly a `some`. -/
def buildOrchComP :
    (Γ : Ctxt jasminDialect) → (sched : List OrchPhase) → (retSlot : Nat) →
    (retTy : JasminTy) → Option (Com jasminDialect Γ retTy)
  | Γ, [], retSlot, retTy =>
      match mkVarSlot Γ retSlot retTy with
      | some v => some (.ret v)
      | none => none
  | Γ, p :: rest, retSlot, retTy =>
      match mkOrchExpr Γ p with
      | none => none
      | some e =>
          match buildOrchComP (p.retTy :: Γ) rest retSlot retTy with
          | some body => some (.var e body)
          | none => none

/-! ### The `extCall` path is byte-unchanged

An all-`call` schedule builds the **identical** `Com` that `buildOrchCom` builds
from the underlying `CallPhase` list — `mkOrchExpr (.call p)` is definitionally
`mkPhaseExpr Γ p`, `OrchPhase.retTy (.call p)` is `p.retTy`, and the two builders
share their recursion shape. So the extension does not perturb the landed EC /
pairing flips: those keep calling `buildOrchCom` on `List CallPhase`, and even if
re-expressed over `OrchPhase` they would build the same `Com`. -/

/-- An all-`call` mixed schedule builds exactly what `buildOrchCom` builds — the
    `extCall` band is byte-identical under the extension. -/
theorem buildOrchComP_call_eq :
    (Γ : Ctxt jasminDialect) → (sched : List CallPhase) → (retSlot : Nat) →
    (retTy : JasminTy) →
    buildOrchComP Γ (sched.map OrchPhase.call) retSlot retTy
      = buildOrchCom Γ sched retSlot retTy
  | _, [], _, _ => rfl
  | Γ, p :: rest, retSlot, retTy => by
      simp only [List.map, buildOrchComP, buildOrchCom, mkOrchExpr]
      cases mkPhaseExpr Γ p with
      | none => rfl
      | some e =>
          simp only [OrchPhase.retTy]
          rw [buildOrchComP_call_eq (p.retTy :: Γ) rest retSlot retTy]
          cases buildOrchCom (p.retTy :: Γ) rest retSlot retTy <;> rfl

/-! ### Denotation and lowering

`buildOrchComP` produces an ordinary `Com jasminDialect`, so its denotation is
the framework's generic `Com.denote` (Core): each new phase's op has a real
denotation in `jasminDenote` — `stackStore` is `stackSet`, `stackLoad` is
`stackGet`, `regConst` is `BitVec.ofNat` — so a mixed schedule denotes
compositionally with no new obligation. LOWERING (corrected 2026-07-04 after the
SDitH/Shake re-source): the word-move phases lower ONLY through the PHYS-ABI path
`VIR.JasminLprogExport.Com.toLprogPhysAbi` / `comToLfundefPhysAbi`, whose per-op
`opToLinstrR` maps `stackStore` to a `STOREIDX` word-move, `stackLoad` to a
`LOADIDX`, `regConst` to a `MOV`, and `extCall` to an `Lcall` — emitting exactly
the interleaved word-moves-around-`Lcall` a sponge needs. The array-ABI path
`Com.toLprogArrAbi` (`ArrAbiOrch.comArrRecords`) does NOT work here: it records
ONLY `extCall` bindings and silently drops `stackStore`/`stackLoad`/`regConst`, so
a mixed schedule must NOT be routed through it (an earlier draft of this docstring
wrongly named `toLprogArrAbi` — it is the wrong consumer). The end-to-end
lower-to-`Lprog` correspondence for the word-move phases is an ORCHESTRATOR-VERIFY
step: lower a concrete mixed schedule via `comToLfundefPhysAbi` and byte-KAT the
emitted `.s`. No denotation is stubbed — the compositional `Com.denote` is total. -/

/-! ### Acceptance: a tiny mixed schedule builds to `some`

A three-phase schedule — one `storeWord`, one `call`, one `loadWord` — over the
context `Γ₀ = [reg 64 (value), reg 64 (index), stackArr 64 4 (buffer)]`
(root slots: buffer `= 0`, index `= 1`, value `= 2`):

* `storeWord 64 4 0 1 2` — `buf[idx] := val`, binds the updated buffer at slot `3`;
* `call permute` on `[stackArr 64 4]` at slot `[3]` — binds the permuted buffer at
  slot `4`;
* `loadWord 64 4 4 1` — reads `permuted[idx]`, binds the word (`reg 64`) at slot `5`,
  returned.

`mixedSchedule_isSome` is the generation gate (a `decide`/`rfl`); it demonstrates a
mixed call + word-move schedule resolves. **State only — the orchestrator runs it.** -/

/-- Initial context for the acceptance example: value, index, buffer (root slots
    `2, 1, 0`). -/
def mixedCtxt : Ctxt jasminDialect := [.reg 64, .reg 64, .stackArr 64 4]

/-- A tiny mixed schedule: scatter a word, permute, gather a word. -/
def mixedSchedule : List OrchPhase :=
  [ .storeWord 64 4 0 1 2
  , .call { leaf := "permute", argTys := [.stackArr 64 4], retTy := .stackArr 64 4,
            argSlots := [3] }
  , .loadWord 64 4 4 1 ]

/-- **Generation gate (acceptance).** The extended front resolves a mixed
    call + word-move schedule. Orchestrator-run (`rfl`). -/
theorem mixedSchedule_isSome :
    (buildOrchComP mixedCtxt mixedSchedule 5 (.reg 64)).isSome = true := by rfl

end CatCrypt.Crypto.SecureCompilation.Dialects.OrchestrationFront
