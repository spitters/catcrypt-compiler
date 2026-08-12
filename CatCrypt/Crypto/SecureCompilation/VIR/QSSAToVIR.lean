/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.QuantumDialect
import CatCrypt.Crypto.SecureCompilation.VIR.Regions
import CatCrypt.Quantum.QuantumSSA
import CatCrypt.Quantum.GateUnitarity

set_option autoImplicit false

/-!
# Phase 2: Structural bridge `QuantumSSA.QSProg` → `Com quantumDialect`

Translates the pre-VIR `CatCrypt.Quantum.QuantumSSA.QSProg` IR into the new
`Com quantumDialect` framework at the syntactic level.

## Where the real semantics lives

This file provides only the *structural* translation. The **real** (non-stub)
`QComp` semantics of a `Com quantumDialect` program lives in the sibling file
`QSSAToVIRCircuit.lean` (Phase 3), which exposes:

* `lowerVIRCom : Com quantumDialect Γ t → RegAlloc numQ → Circuit numQ`
* `Com.realDenoteQComp := unitaryDenote ∘ lowerVIRCom`
* `lowerVIRCom_toVIRCom_eq` — the bridge lemma stating that the
  `QSProg → VIR → Circuit` path agrees with the direct
  `QSProg → Circuit` lowering on the well-formed subset.

That file is the canonical answer to "what does a `Com quantumDialect`
program denote to?".

### Why no `DialectDenoteM quantumDialect (QComp d)` instance here

This file deliberately provides no `DialectDenoteM quantumDialect (QComp d)`
instance. Any such instance could only be a placeholder — type-correct but
semantically vacuous, with every program denoting to `qpure ()` — because:

* `DialectDenoteM`'s `denoteM op (args : HVector ⟦·⟧ op.sig) : M ⟦op.ret⟧`
  shape can only see the *values* under args, but `⟦.qubit⟧ = Unit` —
  there are no physical-qubit indices to read off. Reconstructing which
  qubit a gate acts on requires a register allocator over De Bruijn
  indices (see `QSSAToCircuit.RegAlloc`), which doesn't fit inside the
  typeclass signature.
* The Phase-3 file resolves this by giving the dialect a real semantics
  via direct translation into `Circuit numQ`, bypassing `DialectDenoteM`
  entirely. See `QuantumDialect.lean` for the VEIR-DIFF note.

A future Phase-4 refactor that indexes `QTy.qubit` by a physical index
would let us re-install a meaningful `DialectDenoteM` instance — that
remains an open option.

## Deliverables

* `toVIRTy`, `toVIRCtx`, `toVIRVar`: structural translations of the
  `QuantumSSA` type / context / variable algebra to the dialect's
  (which is shaped almost identically).
* `toVIRCom : QSProg Γ t → Option (Com quantumDialect (toVIRCtx Γ)
  (toVIRTy t))`: the program translation. Returns `Option` because
  `QSProg.ifBit` cannot yet be expressed in `Com` (no regions).
* `mkUnitary1Expr`, `mkInitExpr`, `mkUnitary2Expr`: per-op expression
  builders consumed by `toVIRCom` and reused by hand-written VIR
  encodings in `Programs/`.

## VEIR-DIFF (auditable divergences from Catalyst/QSSA/QIRO)

* The dialect uses single-result `Expr`s — 2-qubit gates return
  `pair qubit qubit`, measurement returns `pair bit qubit`. The
  `QSProg.letQ2 / .letMeas` constructors already pre-bind the same
  pair shape, so the translation is a structural 1:1 pass with no
  pair-destructuring rewrites needed.
* `QSProg.ifBit` translates to `none` (the documented Phase-2
  limitation; regions are deferred to Phase 4 per the plan doc).
* `QuantumSSA.QOp.rz θ` carries `θ : ℝ` (noncomputable); the dialect
  exposes both `QOp.rz : Float → QOp` (legacy, computable) and
  `QOp.rzReal : ℝ → QOp` (added 2026-05-14, exact). The Phase-2
  bridge routes `QuantumSSA.QOp.rz θ` to `QuantumDialect.QOp.rzReal θ`
  with **no conversion loss** — see `mkUnitary1Expr` below. The
  `WellFormedForCircuit` subset accordingly admits the `.rz` arm via
  `rzReal`; see `QSSAToVIRCircuit.lean`.

## Out of scope

* Phase 4 multi-result / regions (would let `ifBit` and 2-qubit
  multi-binders translate cleanly).
* Phase 5 Catalyst MLIR emission.

## References

* `CatCrypt/Quantum/QuantumSSA.lean` — source IR
* `CatCrypt/Quantum/GateUnitarity.lean` — `denoteGateU`, `QComp`
* `CatCrypt/Crypto/SecureCompilation/VIR/QuantumDialect.lean` —
  the Phase-1 dialect (this file's import)
* `CatCrypt/Crypto/SecureCompilation/VIR/QSSAToVIRCircuit.lean` —
  the canonical **real** `QComp` semantics path (Phase 3)
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.QSSAToVIR

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.QuantumDialect
open CatCrypt.Quantum CatCrypt.Quantum.QuantumSSA
open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)

-- Phase-2 bridge depends on `QComp.qpure`, which is noncomputable.
noncomputable section

/-! ## 1. Type translation: `QuantumSSA.QTy` → `QuantumDialect.QTy` -/

/-- Translate a `QuantumSSA.QTy` to the dialect's `QTy`. Shape-identical
    except `qureg` is dialect-only (so the translation never returns one). -/
@[reducible] def toVIRTy : CatCrypt.Quantum.QuantumSSA.QTy → QuantumDialect.QTy
  | .qubit => .qubit
  | .bit => .bit
  | .unit => .unit
  | .pair a b => .pair (toVIRTy a) (toVIRTy b)

/-- Translate a context: pointwise type map. -/
@[reducible] def toVIRCtx :
    CatCrypt.Quantum.QuantumSSA.QCtx →
    Ctxt quantumDialect
  | [] => []
  | t :: Γ => toVIRTy t :: toVIRCtx Γ

/-- Translate a `QSProg` De Bruijn variable to a dialect `Var`. -/
def toVIRVar :
    {Γ : CatCrypt.Quantum.QuantumSSA.QCtx} →
    {t : CatCrypt.Quantum.QuantumSSA.QTy} →
    QVar Γ t → Ctxt.Var (d := quantumDialect) (toVIRCtx Γ) (toVIRTy t)
  | _, _, .here => .here
  | _, _, .there v => .there (toVIRVar v)

/-! ## 2. Op tag translation: `QuantumSSA.QOp` → `QuantumDialect.QOp`

`QuantumSSA.QOp` is indexed by its return type; the dialect's `QOp` is
not. The translation drops the index but preserves the gate identity. -/

/-- Unused placeholder: maps any real angle to the `Float` literal `0.0`.

    Superseded by `QuantumDialect.QOp.rzReal : ℝ → QOp`. The Phase-2 bridge
    (`mkUnitary1Expr`) routes `QuantumSSA.QOp.rz θ` straight to
    `QuantumDialect.QOp.rzReal θ` with no conversion loss, so nothing in this
    repository calls `toRzFloat`; it is retained only for API stability. -/
@[reducible]
def toRzFloat (_ : ℝ) : Float := 0.0

/-- Translate a 1-qubit unitary `QOp .qubit` (non-init) to its dialect tag.

    Caller obligation: pass a non-init op (`hadamard`/`pauliX`/…/`rz`).
    The init cases are folded into `.hadamard` as a safe fallback;
    callers never trigger them on well-formed programs. -/
def toVIROpUnitary1 : CatCrypt.Quantum.QuantumSSA.QOp .qubit → QuantumDialect.QOp
  | .hadamard => .hadamard
  | .pauliX => .pauliX
  | .pauliY => .pauliY
  | .pauliZ => .pauliZ
  | .sGate => .sGate
  | .tGate => .tGate
  | .rz θ => .rzReal θ
  | .init0 => .hadamard  -- VEIR-DIFF: unreachable in `letQ` (init lives in `letInit`)
  | .init1 => .hadamard  -- same; placeholder fallback

/-- Translate a 1-qubit init `QOp .qubit` (`init0` / `init1`) to its dialect tag. -/
def toVIROpInit : CatCrypt.Quantum.QuantumSSA.QOp .qubit → QuantumDialect.QOp
  | .init0 => .init0
  | .init1 => .init1
  | _ => .init0  -- placeholder fallback (caller passes init)

/-- Translate a 2-qubit `QOp (.pair .qubit .qubit)` to its dialect tag. -/
def toVIROp2 :
    CatCrypt.Quantum.QuantumSSA.QOp (.pair .qubit .qubit) → QuantumDialect.QOp
  | .cnot => .cnot
  | .cz => .cz

/-! ### Return-type lemmas

These tell Lean that the chosen translation lands at the expected
dialect return type — needed to fill in `Expr.retTy_eq`. -/

theorem toVIROpUnitary1_ret (op : CatCrypt.Quantum.QuantumSSA.QOp .qubit) :
    (toVIROpUnitary1 op).ret = .qubit := by
  cases op <;> rfl

theorem toVIROpInit_ret (op : CatCrypt.Quantum.QuantumSSA.QOp .qubit) :
    (toVIROpInit op).ret = .qubit := by
  cases op <;> rfl

theorem toVIROp2_ret (op : CatCrypt.Quantum.QuantumSSA.QOp (.pair .qubit .qubit)) :
    (toVIROp2 op).ret = .pair .qubit .qubit := by
  cases op <;> rfl

theorem toVIROpUnitary1_sig (op : CatCrypt.Quantum.QuantumSSA.QOp .qubit) :
    (toVIROpUnitary1 op).sig = [.qubit] := by
  cases op <;> rfl

theorem toVIROpInit_sig (op : CatCrypt.Quantum.QuantumSSA.QOp .qubit) :
    (toVIROpInit op).sig = [] := by
  cases op <;> rfl

theorem toVIROp2_sig (op : CatCrypt.Quantum.QuantumSSA.QOp (.pair .qubit .qubit)) :
    (toVIROp2 op).sig = [.qubit, .qubit] := by
  cases op <;> rfl

/-! ## 3. Program translation: `QSProg → Option (Com quantumDialect …)` -/

/-- Helper: build a 1-qubit unitary expression. Case-splits on `op`
    inline to make the `args : HVector` index land at `(opTag).sig`. -/
def mkUnitary1Expr {Γ : CatCrypt.Quantum.QuantumSSA.QCtx}
    (op : CatCrypt.Quantum.QuantumSSA.QOp .qubit)
    (q : QVar Γ .qubit) :
    Expr quantumDialect (toVIRCtx Γ) .qubit :=
  match op with
  | .hadamard =>
      { op := .hadamard, retTy_eq := rfl, args := .cons (toVIRVar q) .nil }
  | .pauliX =>
      { op := .pauliX, retTy_eq := rfl, args := .cons (toVIRVar q) .nil }
  | .pauliY =>
      { op := .pauliY, retTy_eq := rfl, args := .cons (toVIRVar q) .nil }
  | .pauliZ =>
      { op := .pauliZ, retTy_eq := rfl, args := .cons (toVIRVar q) .nil }
  | .sGate =>
      { op := .sGate, retTy_eq := rfl, args := .cons (toVIRVar q) .nil }
  | .tGate =>
      { op := .tGate, retTy_eq := rfl, args := .cons (toVIRVar q) .nil }
  | .rz θ =>
      -- Exact ℝ translation (2026-05-14): no more `toRzFloat` collapse.
      { op := .rzReal θ, retTy_eq := rfl,
        args := .cons (toVIRVar q) .nil }
  -- VEIR-DIFF: `init0/init1` shouldn't appear inside `letQ` (they belong
  -- in `letInit`). We fall through to `hadamard` as a safe placeholder;
  -- well-formed programs never trigger this branch.
  | .init0 =>
      { op := .hadamard, retTy_eq := rfl, args := .cons (toVIRVar q) .nil }
  | .init1 =>
      { op := .hadamard, retTy_eq := rfl, args := .cons (toVIRVar q) .nil }

/-- Helper: build an init expression (zero-ary). -/
def mkInitExpr {Γ : CatCrypt.Quantum.QuantumSSA.QCtx}
    (op : CatCrypt.Quantum.QuantumSSA.QOp .qubit) :
    Expr quantumDialect (toVIRCtx Γ) .qubit :=
  match op with
  | .init0 => { op := .init0, retTy_eq := rfl, args := .nil }
  | .init1 => { op := .init1, retTy_eq := rfl, args := .nil }
  -- VEIR-DIFF: only `init0/init1` belong in `letInit`. Other 1-qubit
  -- ops fall through to `init0` as a safe placeholder.
  | _ => { op := .init0, retTy_eq := rfl, args := .nil }

/-- Helper: build a 2-qubit unitary expression. -/
def mkUnitary2Expr {Γ : CatCrypt.Quantum.QuantumSSA.QCtx}
    (op : CatCrypt.Quantum.QuantumSSA.QOp (.pair .qubit .qubit))
    (q1 q2 : QVar Γ .qubit) :
    Expr quantumDialect (toVIRCtx Γ) (.pair .qubit .qubit) :=
  match op with
  | .cnot =>
      { op := .cnot, retTy_eq := rfl,
        args := .cons (toVIRVar q1) (.cons (toVIRVar q2) .nil) }
  | .cz =>
      { op := .cz, retTy_eq := rfl,
        args := .cons (toVIRVar q1) (.cons (toVIRVar q2) .nil) }

/-- Translate a `QSProg` to a dialect program.

    * `ret v` → `Com.ret`
    * `letQ op q body` → `Com.var` of a 1-qubit gate expression
    * `letQ2 op q1 q2 body` → `Com.var` of a 2-qubit gate expression
      (returns `pair qubit qubit` — single-result with `pair` payload)
    * `letInit op body` → `Com.var` of an `init0/init1` expression
    * `letMeas q body` → `Com.var` of a `measure` expression
      (returns `pair bit qubit`)
    * `ifBit _ _ _` → **`none`** (no regions in `Com` yet; deferred to
      Phase 4 per the plan doc).

    All non-`ifBit` programs translate successfully. -/
def toVIRCom :
    {Γ : CatCrypt.Quantum.QuantumSSA.QCtx} →
    {t : CatCrypt.Quantum.QuantumSSA.QTy} →
    QSProg Γ t → Option (Com quantumDialect (toVIRCtx Γ) (toVIRTy t))
  | _, _, .ret v => some (.ret (toVIRVar v))
  | _, _, .letQ op q body =>
      match toVIRCom body with
      | some body' => some (.var (mkUnitary1Expr op q) body')
      | none => none
  | _, _, .letQ2 op q1 q2 body =>
      match toVIRCom body with
      | some body' => some (.var (mkUnitary2Expr op q1 q2) body')
      | none => none
  | _, _, .letInit op body =>
      match toVIRCom body with
      | some body' => some (.var (mkInitExpr op) body')
      | none => none
  | _, _, .letMeas q body =>
      match toVIRCom body with
      | some body' =>
          let e : Expr quantumDialect (toVIRCtx _) (.pair .bit .qubit) :=
            { op := .measure
              retTy_eq := rfl
              args := .cons (toVIRVar q) .nil }
          some (.var e body')
      | none => none
  | _, _, .ifBit _ _ _ => none  -- Phase-2 limitation: regions deferred

/-! ### Region-extended translation `toVIRComR`

`toVIRCom` returns `none` on `QSProg.ifBit` (no region constructor in
`Com quantumDialect`). The region-extended dialect program type
`ComR quantumDialect`, defined in `VIR/Regions.lean`, adds a single
`ifBit` constructor — `toVIRComR` exploits that to translate `ifBit`
nodes structurally.

**SecretLevel policy.** The `lvl : SecretLevel` argument of `ComR.ifBit`
is *caller-asserted* information about whether the scrutinee's value
flow is public or secret. We default to `.Secret`, which is the
**conservative** choice: a `.Secret` tag forces any constant-time
predicate to reject programs that branch on this bit unless the caller
has discharged the flow obligation through a separate analysis (e.g.,
a Phase-J "measurement-output-is-public" rewriter). Marking a secret
bit as `.Public` would silently weaken CT guarantees, so we never do
it by default.

A future Phase-5 pass can rewrite measurement-derived bits whose flow
the caller declares public — at that point the default here becomes
moot. -/

/-- Translate a `QSProg` into the region-extended dialect program type
`ComR quantumDialect`. Mirrors `toVIRCom` on every non-`ifBit`
constructor (delegating to it and lifting via `ComR.ofCom`), and
translates `QSProg.ifBit` structurally to `ComR.ifBit` with
`SecretLevel.Secret` (the conservative default — see docstring above).

Returns `none` only if a sub-translation does (e.g., a body containing
an `rz` placeholder that ultimately can't be expressed; in practice
this only happens if an inner non-`ifBit` constructor's body fails). -/
def toVIRComR :
    {Γ : CatCrypt.Quantum.QuantumSSA.QCtx} →
    {t : CatCrypt.Quantum.QuantumSSA.QTy} →
    QSProg Γ t → Option (ComR quantumDialect (toVIRCtx Γ) (toVIRTy t))
  | _, _, .ret v => some (.ret (toVIRVar v))
  | _, _, .letQ op q body =>
      match toVIRComR body with
      | some body' => some (.var (mkUnitary1Expr op q) body')
      | none => none
  | _, _, .letQ2 op q1 q2 body =>
      match toVIRComR body with
      | some body' => some (.var (mkUnitary2Expr op q1 q2) body')
      | none => none
  | _, _, .letInit op body =>
      match toVIRComR body with
      | some body' => some (.var (mkInitExpr op) body')
      | none => none
  | _, _, .letMeas q body =>
      match toVIRComR body with
      | some body' =>
          let e : Expr quantumDialect (toVIRCtx _) (.pair .bit .qubit) :=
            { op := .measure
              retTy_eq := rfl
              args := .cons (toVIRVar q) .nil }
          some (.var e body')
      | none => none
  | _, _, .ifBit cond thenBr elseBr =>
      match toVIRComR thenBr, toVIRComR elseBr with
      | some t', some e' =>
          some (.ifBit (toVIRVar cond) SecretLevel.Secret t' e')
      | _, _ => none

/-! ## 4. Bell-pair smoke test

A small program: `init0; init0; H q1; CNOT q1 q2; ret`. Verifies the
translation succeeds.

The real `QComp` semantics for VIR programs is provided in
`QSSAToVIRCircuit.lean` via `Com.realDenoteQComp`. The earlier
`DialectDenoteM (QComp d)` placeholder instance — which routed every
op to `QComp.qpure (default)` — has been removed (see module
docstring); accordingly the equivalence smoke check between two
denotations of the bell pair has been removed as well. -/

namespace SmokeTest

/-- Bell-pair program written here (mirrors `QuantumSSA.bellPair`).
    Inlined rather than re-using `QuantumSSA.bellPair` because the
    upstream value lives in a `noncomputable section`, which prevents
    `decide` from reducing the translation result. -/
def bellPair : QSProg [] (.pair .qubit .qubit) :=
  .letInit .init0 <|                           -- q₁ = |0⟩
  .letInit .init0 <|                           -- q₂ = |0⟩
  .letQ .hadamard (.there .here) <|            -- q₁' = H(q₁)
  .letQ2 .cnot .here (.there (.there .here)) <| -- (q₁'', q₂') = CNOT(q₁', q₂)
  .ret .here

/-- The bell-pair program translates successfully (no `ifBit`).
    Direct computation through the `Option` `match` chain. -/
theorem bellPair_isSome : (toVIRCom bellPair).isSome := by
  simp [bellPair, toVIRCom]

/-- The translated dialect program. -/
def bellPairVIR : Com quantumDialect [] (toVIRTy (.pair .qubit .qubit)) :=
  (toVIRCom bellPair).get bellPair_isSome

/-- Region smoke test: a `QSProg` containing `ifBit` translates via
`toVIRComR` to `some _`, whereas `toVIRCom` returns `none`. The
program assumes a classical bit is already in scope (`[.bit]`):
branch on it; either arm initialises a `|0⟩` and returns. -/
def branchOnBit : QSProg [.bit] .qubit :=
  .ifBit .here
    (.letInit .init0 (.ret .here))
    (.letInit .init1 (.ret .here))

/-- `toVIRCom` rejects `ifBit` (returns `none`). -/
example : toVIRCom branchOnBit = none := rfl

/-- `toVIRComR` accepts `ifBit` (returns `some _`). -/
theorem branchOnBit_R_isSome : (toVIRComR branchOnBit).isSome := by
  simp [branchOnBit, toVIRComR]

/-! ### Smoke test for the exact-ℝ `rz → rzReal` routing (2026-05-14)

A tiny `QSProg` with a non-zero `Rz(π/4)` angle. We verify that
`toVIRCom` produces a `Com` whose lone gate-bearing expression carries
`QOp.rzReal (Real.pi / 4)` — the angle is preserved, not collapsed to
`0.0` via the legacy `toRzFloat` path. -/

/-- A 1-qubit program: `init0; Rz(π/4) q; ret`. -/
def rzQuarterPi : QSProg [] .qubit :=
  .letInit .init0 <|
  .letQ (.rz (Real.pi / 4)) .here <|
  .ret .here

/-- The expected VIR target: the same shape, with `rzReal` carrying
    the exact ℝ angle. -/
def rzQuarterPiVIR : Com quantumDialect [] .qubit :=
  .var ({ op := .init0, retTy_eq := rfl, args := .nil }) <|
  .var ({ op := .rzReal (Real.pi / 4), retTy_eq := rfl,
          args := .cons .here .nil }) <|
  .ret .here

/-- Translation preserves the rotation angle exactly. -/
theorem rzQuarterPi_toVIRCom :
    toVIRCom rzQuarterPi = some rzQuarterPiVIR := rfl

end SmokeTest

end -- noncomputable section

end CatCrypt.Crypto.SecureCompilation.VIR.QSSAToVIR
