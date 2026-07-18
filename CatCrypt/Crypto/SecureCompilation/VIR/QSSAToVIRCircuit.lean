/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.QSSAToVIR
import CatCrypt.Quantum.QSSAToCircuit
import CatCrypt.Quantum.GateUnitarity

set_option autoImplicit false

/-!
# Phase 3: real-semantics bridge `Com quantumDialect → Circuit numQ`

The Phase-1 / Phase-2 files install dialect denotations that route every
op to `QComp.qpure (default)` — semantically vacuous (every program
denotes to `qpure ()`). The architectural reason: `QTy.denote .qubit = Unit`,
so `DialectDenoteM` args don't carry physical qubit indices.

This file closes the gap by giving the dialect a **real** semantics via
a direct translation to the existing `CatCrypt.Quantum.QCircuit.Circuit`
type, which denotes through `unitaryDenote`. The translation parallels
`QSSAToCircuit.lowerProg`, and we prove the two translations commute —
i.e. the `QSProg → VIR → Circuit` path lands at the same circuit as the
`QSProg → Circuit` path. This realises Phase 3 of the quantum VIR work.

## Pipeline

```
QSProg Γ t  ─(toVIRCom)─▶  Option (Com quantumDialect (toVIRCtx Γ) (toVIRTy t))
   │                                 │
   │ lowerProg                       │ lowerVIRCom
   ▼                                 ▼
Circuit numQ  ◀─────(equal, lowerVIRCom_toVIRCom_eq)─── Option (Circuit numQ)
   │
   │ unitaryDenote
   ▼
QComp (2^numQ) Unit
```

## Key results

* `lowerVIRCom` — direct lowering `Com quantumDialect → Circuit numQ`
  using `QSSAToCircuit.RegAlloc`.
* `Com.realDenoteQComp` — real `QComp (2^numQ) Unit` semantics as
  `unitaryDenote ∘ lowerVIRCom`.
* `lowerVIRCom_toVIRCom_eq` — translation commutes with `lowerProg`.

## VEIR-DIFF

The new denotation isn't installed as a `DialectDenoteM` instance because
the typeclass forces `op → args → M ⟦ret⟧` and `⟦.qubit⟧ = Unit`. Phase 4
(qubit indices in the type denotation) would let us route through
`Com.denoteM` again. Until then, `lowerVIRCom + unitaryDenote` is the
canonical real-semantics path.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.QSSAToVIRCircuit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.QuantumDialect
open CatCrypt.Crypto.SecureCompilation.VIR.QSSAToVIR
open CatCrypt.Quantum CatCrypt.Quantum.QSSAToCircuit
open CatCrypt.Quantum.QCircuit

noncomputable section

/-! ## 1. Variable → physical qubit lookup -/

/-- Extract the De Bruijn index from a VIR `Var Γ t`. Mirrors
    `QSSAToCircuit.qvarIndex`. -/
def virVarIndex {Γ : Ctxt quantumDialect} {t : QTy} :
    Ctxt.Var (d := quantumDialect) Γ t → ℕ
  | .here => 0
  | .there v => 1 + virVarIndex v

/-- Pointwise: `virVarIndex` of the translated variable equals `qvarIndex`. -/
theorem virVarIndex_toVIRVar
    {Γ : CatCrypt.Quantum.QuantumSSA.QCtx}
    {t : CatCrypt.Quantum.QuantumSSA.QTy} (v : QuantumSSA.QVar Γ t) :
    virVarIndex (toVIRVar v) = qvarIndex v := by
  induction v with
  | here => rfl
  | there v ih =>
      show virVarIndex (.there (toVIRVar v)) = 1 + qvarIndex v
      show 1 + virVarIndex (toVIRVar v) = 1 + qvarIndex v
      rw [ih]

/-! ## 2. Dialect op → `Gate numQ` -/

/-- Single-qubit dialect op → `Gate numQ`. The legacy `rz : Float` arm
    still collapses to `Rz i 0` (no `Float → ℝ` exists in this file).
    The new `rzReal : ℝ` arm (2026-05-14) routes the exact angle into
    `Gate.Rz i θ`. -/
def virQOpToGate1 {numQ : ℕ} (op : QuantumDialect.QOp) (i : Fin numQ) :
    Option (Gate numQ) :=
  match op with
  | .hadamard  => some (.H i)
  | .pauliX    => some (.X i)
  | .pauliY    => some (.Y i)
  | .pauliZ    => some (.Z i)
  | .sGate     => some (.S i)
  | .tGate     => some (.T i)
  | .rz _      => some (.Rz i 0)        -- legacy Float arm: collapses (no Float→ℝ)
  | .rzReal θ  => some (.Rz i θ)        -- exact-ℝ arm: angle preserved
  | _          => none

/-- Two-qubit dialect op → `Gate numQ`. -/
def virQOpToGate2 {numQ : ℕ} (op : QuantumDialect.QOp) (i j : Fin numQ) :
    Option (Gate numQ) :=
  match op with
  | .cnot => some (.CNOT i j)
  | .cz   => some (.CZ i j)
  | _     => none

/-! ## 3. `Com quantumDialect → Circuit numQ` lowering -/

/-- Pull out the physical-qubit lookup + gate emission. Returns:
    * `gateOpt` — the optional gate to emit
    * `bindQ` — the physical qubit assigned to the bound result var

    The nested match on `e.op, e.args` is exhaustive because the dialect's
    `sig` enforces the args' length for each op tag. Where args are
    irrelevant (zero-ary or "discard"-style ops), we match `_` and bind
    the result to physical qubit 0 (arbitrary). -/
def lowerExpr {numQ : ℕ} (hpos : 0 < numQ) {Γ : Ctxt quantumDialect} {t : QTy}
    (ra : RegAlloc numQ) (e : Expr quantumDialect Γ t) :
    Option (Gate numQ) × Fin numQ :=
  -- Returns (optional gate to emit, physical qubit for the bound result).
  match e.op, e.args with
  | .init0, _ => (none, ⟨0, hpos⟩)
  | .init1, _ => (none, ⟨0, hpos⟩)
  | .hadamard, .cons v _ =>
      let q := ra.lookup (virVarIndex v); (some (.H q), q)
  | .pauliX, .cons v _ =>
      let q := ra.lookup (virVarIndex v); (some (.X q), q)
  | .pauliY, .cons v _ =>
      let q := ra.lookup (virVarIndex v); (some (.Y q), q)
  | .pauliZ, .cons v _ =>
      let q := ra.lookup (virVarIndex v); (some (.Z q), q)
  | .sGate, .cons v _ =>
      let q := ra.lookup (virVarIndex v); (some (.S q), q)
  | .tGate, .cons v _ =>
      let q := ra.lookup (virVarIndex v); (some (.T q), q)
  | .rz _, .cons v _ =>
      let q := ra.lookup (virVarIndex v); (some (.Rz q 0), q)
  | .rzReal θ, .cons v _ =>
      let q := ra.lookup (virVarIndex v); (some (.Rz q θ), q)
  | .cnot, .cons v₁ (.cons v₂ _) =>
      let q1 := ra.lookup (virVarIndex v₁)
      let q2 := ra.lookup (virVarIndex v₂)
      (some (.CNOT q1 q2), q1)
  | .cz, .cons v₁ (.cons v₂ _) =>
      let q1 := ra.lookup (virVarIndex v₁)
      let q2 := ra.lookup (virVarIndex v₂)
      (some (.CZ q1 q2), q1)
  | .measure, .cons v _ =>
      let q := ra.lookup (virVarIndex v); (some (.Meas q), q)
  | .discard, _ => (none, ⟨0, hpos⟩)
  | .genericGate _ _, _ => (none, ⟨0, hpos⟩)
  | .adjoint _, _ => (none, ⟨0, hpos⟩)
  | .controlled _, _ => (none, ⟨0, hpos⟩)

/-- Direct lowering of a VIR `Com quantumDialect` to a `Circuit numQ`,
    indexed by a `RegAlloc`. Mirrors `QSSAToCircuit.lowerProg` op-by-op.

    The translation **never returns `none`** (unlike `QSSAToCircuit.lowerProg`
    which is conditional on `isMeasFree`): the VIR `measure` op simply emits
    a `Gate.Meas` whose `unitaryDenote` is the identity channel. -/
def lowerVIRCom {numQ : ℕ} (hpos : 0 < numQ) :
    {Γ : Ctxt quantumDialect} → {t : QTy} →
    Com quantumDialect Γ t → RegAlloc numQ → Circuit numQ
  | _, _, .ret _, _ => .empty
  | _, _, .var e body, ra =>
    let (gateOpt, bindQ) := lowerExpr hpos ra e
    let body' := lowerVIRCom hpos body (ra.extend bindQ)
    match gateOpt with
    | some g => .gate g body'
    | none => body'

/-! ## 4. Real-semantics denotation for the dialect

The real semantics is `unitaryDenote ∘ lowerVIRCom`. -/

/-- Real `QComp` semantics of a `Com quantumDialect`: lower to circuit,
    then apply `unitaryDenote`. Replaces the Phase-2 stub
    `QOp.denoteQComp` (which routed every op to `qpure ()`). -/
def Com.realDenoteQComp {numQ : ℕ} (hpos : 0 < numQ)
    {Γ : Ctxt quantumDialect} {t : QTy} (c : Com quantumDialect Γ t)
    (ra : RegAlloc numQ) : QComp (2 ^ numQ) Unit :=
  GateUnitarity.unitaryDenote (lowerVIRCom hpos c ra)

/-! ## 5. Well-formed subset

The Phase 2 bridge has documented placeholder behaviour for one remaining
VEIR-DIFF (see `QSSAToVIR.lean`):

* `.init0` / `.init1` *inside* a `letQ` (instead of `letInit`) —
  `mkUnitary1Expr` falls back to `.hadamard`.

The previous `.rz θ` VEIR-DIFF (collapse to `0.0` via `toRzFloat`) is
**closed** as of 2026-05-14: `mkUnitary1Expr` now routes
`QuantumSSA.QOp.rz θ` to `QuantumDialect.QOp.rzReal θ` and
`lowerVIRCom` lowers `rzReal θ` to `Gate.Rz q θ` exactly.

Programs in `WellFormedForCircuit` avoid the remaining placeholders;
the bridge commutes exactly on this subset. Deutsch-Jozsa, Grover,
Bell, and most non-trivial circuits live in the subset. -/

/-- A QSSA 1-qubit `QOp` is "circuit-friendly" if it's not an
    out-of-place `.init0` / `.init1`.
    Note (2026-05-14): the previous `.rz _ => False` exclusion was
    removed once the dialect grew an exact-ℝ `rzReal` constructor;
    `mkUnitary1Expr` now lowers `.rz θ` faithfully via `rzReal θ`. -/
def QOpCircuitFriendly : QuantumSSA.QOp .qubit → Prop
  | .init0 => False
  | .init1 => False
  | _ => True

/-- A QSSA 1-qubit `QOp` is an init constructor. -/
def QOpIsInit : QuantumSSA.QOp .qubit → Prop
  | .init0 | .init1 => True
  | _ => False

/-- Programs free of the Phase-2 placeholder cases. -/
def WellFormedForCircuit :
    {Γ : CatCrypt.Quantum.QuantumSSA.QCtx} →
    {t : CatCrypt.Quantum.QuantumSSA.QTy} →
    QuantumSSA.QSProg Γ t → Prop
  | _, _, .ret _ => True
  | _, _, .letQ op _ body => QOpCircuitFriendly op ∧ WellFormedForCircuit body
  | _, _, .letQ2 _ _ _ body => WellFormedForCircuit body
  | _, _, .letInit op body => QOpIsInit op ∧ WellFormedForCircuit body
  | _, _, .letMeas _ body => WellFormedForCircuit body
  | _, _, .ifBit _ _ _ => False

/-! ## 6. Equivalence with `QSSAToCircuit.lowerProg`

The key technical lemma: lowering through VIR commutes with the direct
`QSProg → Circuit` lowering, on the well-formed subset. -/

/-- Translation commutativity. -/
theorem lowerVIRCom_toVIRCom_eq {numQ : ℕ} (hpos : 0 < numQ)
    {Γ : CatCrypt.Quantum.QuantumSSA.QCtx} {t : CatCrypt.Quantum.QuantumSSA.QTy}
    (p : QuantumSSA.QSProg Γ t) (hmf : p.isMeasFree)
    (hwf : WellFormedForCircuit p) (ra : RegAlloc numQ) :
    ∃ c, toVIRCom p = some c ∧
      lowerVIRCom hpos c ra = lowerProg numQ hpos ra p hmf := by
  induction p generalizing ra with
  | ret v =>
      refine ⟨.ret (toVIRVar v), rfl, rfl⟩
  | letQ op q body ih =>
      have hwf_body : WellFormedForCircuit body := hwf.2
      have hop_friendly := hwf.1
      obtain ⟨c, hc, hcEq⟩ := ih hmf hwf_body (ra.extend (ra.lookup (qvarIndex q)))
      refine ⟨.var (mkUnitary1Expr op q) c, ?_, ?_⟩
      · simp [toVIRCom, hc]
      · cases op with
        | hadamard =>
            simp only [lowerVIRCom, mkUnitary1Expr, lowerExpr, lowerProg,
              qopToGate1, virVarIndex_toVIRVar, hcEq]
        | pauliX =>
            simp only [lowerVIRCom, mkUnitary1Expr, lowerExpr, lowerProg,
              qopToGate1, virVarIndex_toVIRVar, hcEq]
        | pauliY =>
            simp only [lowerVIRCom, mkUnitary1Expr, lowerExpr, lowerProg,
              qopToGate1, virVarIndex_toVIRVar, hcEq]
        | pauliZ =>
            simp only [lowerVIRCom, mkUnitary1Expr, lowerExpr, lowerProg,
              qopToGate1, virVarIndex_toVIRVar, hcEq]
        | sGate =>
            simp only [lowerVIRCom, mkUnitary1Expr, lowerExpr, lowerProg,
              qopToGate1, virVarIndex_toVIRVar, hcEq]
        | tGate =>
            simp only [lowerVIRCom, mkUnitary1Expr, lowerExpr, lowerProg,
              qopToGate1, virVarIndex_toVIRVar, hcEq]
        | rz θ =>
            -- 2026-05-14: exact-ℝ via `rzReal`; commutes with `qopToGate1 .rz θ`.
            simp only [lowerVIRCom, mkUnitary1Expr, lowerExpr, lowerProg,
              qopToGate1, virVarIndex_toVIRVar, hcEq]
        | init0 => simp [QOpCircuitFriendly] at hop_friendly
        | init1 => simp [QOpCircuitFriendly] at hop_friendly
  | letQ2 op q1 q2 body ih =>
      have hwf_body : WellFormedForCircuit body := hwf
      obtain ⟨c, hc, hcEq⟩ := ih hmf hwf_body
                                  (ra.extend (ra.lookup (qvarIndex q1)))
      refine ⟨.var (mkUnitary2Expr op q1 q2) c, ?_, ?_⟩
      · simp [toVIRCom, hc]
      · cases op <;>
          simp [lowerVIRCom, lowerProg, mkUnitary2Expr, qopToGate2,
                lowerExpr, virVarIndex_toVIRVar, hcEq]
  | letInit op body ih =>
      have hwf_body : WellFormedForCircuit body := hwf.2
      have hop_init := hwf.1
      obtain ⟨c, hc, hcEq⟩ := ih hmf hwf_body (ra.extend ⟨0, hpos⟩)
      refine ⟨.var (mkInitExpr op) c, ?_, ?_⟩
      · simp [toVIRCom, hc]
      · cases op with
        | init0 =>
            simp only [lowerVIRCom, mkInitExpr, lowerExpr, lowerProg, hcEq]
        | init1 =>
            simp only [lowerVIRCom, mkInitExpr, lowerExpr, lowerProg, hcEq]
        | _ => simp [QOpIsInit] at hop_init
  | letMeas q body ih =>
      exact absurd hmf (by simp [QuantumSSA.QSProg.isMeasFree])
  | ifBit _ _ _ _ _ =>
      -- Excluded by `WellFormedForCircuit`.
      exact absurd hwf (by simp [WellFormedForCircuit])

end

end CatCrypt.Crypto.SecureCompilation.VIR.QSSAToVIRCircuit
