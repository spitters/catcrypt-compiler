/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.Core
public import CatCrypt.Crypto.SecureCompilation.VIR.CoreM
public import Mathlib.Data.Real.Basic

@[expose] public section

set_option autoImplicit false

/-!
# Quantum dialect over VIR (Phase 1)

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

A `VIR.Dialect` whose `Op`/`Ty` mirror the existing `CatCrypt.Quantum.QuantumSSA`
ops, plus the additions identified by the prior-art survey:

* `genericGate name params` — Catalyst-style extensibility escape hatch
* `adjoint op` / `controlled op` — IR-level gate transformations
* `qureg n` type — register type for variable-width algorithms

## Scope of this file (Phase 1)

* Op enum + Ty enum
* `DialectSignature` mapping
* No `DialectDenoteM` instance: the dialect's semantics is the lowering into
  the circuit model (see the VEIR-DIFF entry below)

Phase 2 (separate file `VIR/QSSAToVIR.lean`) bridges to the real unitary
semantics from `CatCrypt/Quantum/GateUnitarity.lean`. This file does not
import any `CatCrypt.Quantum.*` module — that contract avoids accidentally
coupling the IR layer to the existing pure-state model.

## VEIR-DIFF (auditable divergences from Catalyst/QSSA/QIRO)

* Single-return `Expr` shape: 2-qubit gates return `pair qubit qubit`
  rather than two-result ops. The plan defers this ("until effectful VIR
  has multi-result ops") as a Phase 2+ follow-up; until then, `pair` is
  the workaround.
* No memory-semantics / value-semantics split (QIRO has two dialects;
  we keep one). Memory semantics is parked until a real hax/Q# extraction
  source materializes — see plan §"Optional: QIRO-style two-dialect split".
* `adjoint` / `controlled` are *non-recursive* IR constructors carrying
  another `QOp` payload (one level of nesting; deeper nesting is fine via
  the inductive shape but no recursion lemma is yet exposed).
* `genericGate` carries `(name, params)` payload; its semantics is
  deliberately a no-op stub in this file. Lowering paths that need a
  concrete unitary register a new per-gate constructor instead.
* The operation semantics lives in
  `CatCrypt/Crypto/Quantum/VIR/QuantumDialectDenote.lean`: a `DialectDenoteM`
  value over the type denotation `QTy.phys numQ`, in which a qubit denotes its
  physical wire. That type denotation is passed explicitly; `QTy.denote` below is
  the default one, with nominal qubit handles. On programs the lowering
  translates exactly, the semantics agrees with
  `Com.realDenoteQComp := unitaryDenote ∘ lowerVIRCom`
  (`Com.denoteQ_forget_eq_realDenoteQComp`).

## References

* `CatCrypt/Quantum/QuantumSSA.lean` — pre-VIR `QOp`/`QTy` shape
* `CatCrypt/Crypto/SecureCompilation/VIR/CatCryptDialect.lean` — the
  reference pattern for a VIR-shaped dialect
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.QuantumDialect

open CatCrypt.Crypto.SecureCompilation.VIR

/-! ## 1. Type system -/

/-- Types in the quantum dialect.

    Mirrors `CatCrypt.Quantum.QuantumSSA.QTy` plus the `qureg n` register
    type recommended by the prior-art survey (Catalyst / QIRO both expose
    a register type). -/
inductive QTy where
  /-- Single qubit. Linear (must be used exactly once). -/
  | qubit
  /-- Classical bit, e.g., a measurement outcome. -/
  | bit
  /-- Unit type. -/
  | unit
  /-- Pair of types. Used for multi-output ops like `measure : qubit →
      pair bit qubit`. -/
  | pair (a b : QTy)
  /-- Register of `n` qubits. VEIR-DIFF: Catalyst / QIRO call this
      `!quantum.reg`. -/
  | qureg (n : Nat)
  deriving DecidableEq, Repr

/-! ## 2. Op tags -/

/-- Quantum operation tags.

    Mirrors `CatCrypt.Quantum.QuantumSSA.QOp` plus the additions identified
    by the prior-art survey:

    * `genericGate name params` — Catalyst's `quantum.custom` analogue;
      acts as an escape hatch for lowering paths that need a gate without
      a verified per-constructor semantics.
    * `adjoint op` / `controlled op` — IR-level transformations exposed
      by both Catalyst and QIRO. One level of nesting is enough to cover
      the common cases (`adjoint hadamard`, `controlled rz θ`, …).

    Note: 2-qubit gates (`cnot`, `cz`) keep `pair qubit qubit` as their
    return shape; multi-result binders are deferred to Phase 2 per the
    plan doc. -/
inductive QOp where
  /-- Initialize a fresh qubit in |0⟩. -/
  | init0
  /-- Initialize a fresh qubit in |1⟩. -/
  | init1
  /-- Hadamard gate. -/
  | hadamard
  /-- Pauli-X gate. -/
  | pauliX
  /-- Pauli-Y gate. -/
  | pauliY
  /-- Pauli-Z gate. -/
  | pauliZ
  /-- S gate (phase π/2). -/
  | sGate
  /-- T gate (phase π/4). -/
  | tGate
  /-- `Rz(θ)` rotation, `Float`-parametrised (computable). Retained for
      backward compatibility with hand-written VIR programs that use a
      concrete `Float` angle. Lowering paths that need an exact angle
      should use `rzReal` instead. -/
  | rz (θ : Float)
  /-- `Rz(θ)` rotation, `ℝ`-parametrised (noncomputable, exact). Added
      2026-05-14 alongside `rz` to replace the lossy `ℝ → Float`
      collapse used by the Phase-2 bridge (`QSSAToVIR.toRzFloat`).
      Routes to `Quantum.Circuit.Gate.Rz : Fin n → ℝ → Gate n`. -/
  | rzReal (θ : ℝ)
  /-- CNOT. -/
  | cnot
  /-- Controlled-Z. -/
  | cz
  /-- Computational-basis measurement. -/
  | measure
  /-- Discard / trace out a qubit. -/
  | discard
  /-- Extensibility escape hatch: a named gate with real parameters
      (Catalyst `quantum.custom`-style). Semantics is opaque at this
      layer; lowering paths must supply it. -/
  | genericGate (name : String) (params : List Float)
  /-- IR-level adjoint of another op. One level of nesting. -/
  | adjoint (op : QOp)
  /-- IR-level controlled version of another op. One level of nesting. -/
  | controlled (op : QOp)

/-! ## VEIR-DIFF: `Float` vs `ℝ` — RESOLVED via `rzReal`

The plan doc spec'd `rz (θ : ℝ)` to match `QuantumSSA.QOp.rz`. The
original `rz` constructor uses `Float` so that `QOp` itself is
computable (`decide`/`rfl` work on dialect programs).

As of 2026-05-14 we ship an additional `rzReal (θ : ℝ)` constructor
so the Phase-2 bridge (`QSSAToVIR.lean`) can route
`QuantumSSA.QOp.rz (θ : ℝ)` to `QuantumDialect.QOp.rzReal θ` without
any conversion loss. `QOp` carries `Real`, which is noncomputable, but
existing pattern matches over `QOp` that don't touch `rzReal` still
reduce by `rfl` — the noncomputability is local to the `rzReal` arm.

Approach picked: **A** (add `rzReal` alongside `rz`). Pros: zero blast
radius for callers using `Float` (QFT-2 hand-encoding still type-checks
`as-is`); the exact-ℝ path coexists. Cons: dialect Op enum has two `Rz`
constructors; downstream code must handle both. The alternative was
Approach B (replace `rz : Float` with `rz : ℝ`, accepting `noncomputable`
cascading) — rejected as too invasive given the existing hand-written
VIR programs.
-/

/-! ## 3. The dialect -/

/-- The quantum dialect: Ops are `QOp`, Ty is `QTy`. -/
@[reducible] def quantumDialect : Dialect :=
  { Op := QOp, Ty := QTy }

/-! ## 4. `TyDenote`: each `QTy` to a stub Lean type

Phase 1 placeholders only. Phase 2 will replace `qubit` with a real
quantum-state carrier (probably indexing into a `QComp n`). -/

/-- Phase 1 placeholder denotations. -/
@[reducible] def QTy.denote : QTy → Type
  | .qubit => Unit
  | .bit => Bool
  | .unit => Unit
  | .pair a b => QTy.denote a × QTy.denote b
  | .qureg n => Fin n → Unit

@[reducible] instance : TyDenote QTy where
  denote := QTy.denote

/-! ## 5. Op signatures -/

/-- Argument types of an op. -/
def QOp.sig : QOp → List QTy
  | .init0 | .init1 => []
  | .hadamard | .pauliX | .pauliY | .pauliZ | .sGate | .tGate
  | .rz _ | .rzReal _ =>
      [.qubit]
  | .cnot | .cz => [.qubit, .qubit]
  | .measure => [.qubit]
  | .discard => [.qubit]
  | .genericGate _ _ => []  -- VEIR-DIFF: variadic not modelled in Phase 1
  | .adjoint op | .controlled op => op.sig

/-- Return type of an op. -/
def QOp.ret : QOp → QTy
  | .init0 | .init1 => .qubit
  | .hadamard | .pauliX | .pauliY | .pauliZ | .sGate | .tGate
  | .rz _ | .rzReal _ =>
      .qubit
  | .cnot | .cz => .pair .qubit .qubit
  | .measure => .pair .bit .qubit
  | .discard => .unit
  | .genericGate _ _ => .unit  -- VEIR-DIFF: opaque-signature ops return unit
  | .adjoint op => op.ret
  | .controlled op => op.ret  -- VEIR-DIFF: real lowering would prepend a control wire

instance : DialectSignature quantumDialect where
  sig := QOp.sig
  ret := QOp.ret

end CatCrypt.Crypto.SecureCompilation.VIR.QuantumDialect
