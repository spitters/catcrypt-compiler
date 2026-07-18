/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.MultiCom
import CatCrypt.Crypto.SecureCompilation.VIR.QuantumDialect
import CatCrypt.Crypto.SecureCompilation.VIR.QSSAToVIRCircuit

set_option autoImplicit false

/-!
# `MultiCom` setup for `quantumDialect` (Phase 4 #7)

Wires the `PairDialect` typeclass for `quantumDialect` and provides a
multi-binder lowering `lowerMultiVIRCom : ComMulti quantumDialect Γ t →
RegAlloc numQ → Circuit numQ` that mirrors `lowerVIRCom` from
`QSSAToVIRCircuit.lean` and handles the new `letProj` case.

The original `letProj` lowering rule (the *demo* allocator,
`lowerMultiVIRCom`) routes both projections to the **same** physical
qubit slot as the parent pair binding. That is sufficient for the QFT-2
SWAP demo: with the identity allocator all wires collapse to physical
qubit `0`, and the three trailing CNOTs all act on `(0, 0)`.

For arbitrary 2-qubit gate sequences (e.g. `letProj` after CNOT followed
by independent ops on the two outputs), the demo allocator aliases the
qubits incorrectly. The *pair-aware* allocator
(`PairAwareAlloc` + `lowerMultiVIRCom_pairAware`, added 2026-05-15)
records the two output physical slots of every 2-qubit op and routes
the two `letProj` projections to **distinct** slots on lookup.

Both lowerings are kept side-by-side: the QFT-2 `rfl` proof continues
to hold for the demo allocator, and the pair-aware variant is the new
default for non-degenerate cases. See §"Pair-aware allocator" below.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.QuantumDialect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Quantum.QCircuit

/-! ## 1. `PairDialect` instance for `quantumDialect` -/

instance : PairDialect quantumDialect where
  pairTy := .pair
  proj₁ := Prod.fst
  proj₂ := Prod.snd

/-! ## 2. Multi-binder lowering — *demo* allocator -/

/-- Direct lowering of a `ComMulti quantumDialect` to a `Circuit numQ`.

    Mirrors `lowerVIRCom` for the `ret` / `var` cases, and additionally
    handles `letProj`: the body is lowered in a context extended twice
    (once per projection). Both projections of a pair-typed binding are
    routed to the same physical qubit `pairQ` — the identity allocator
    already collapses all wires, so this loses no information at the
    Phase-3 demo level. -/
def lowerMultiVIRCom {numQ : ℕ} (hpos : 0 < numQ) :
    {Γ : Ctxt quantumDialect} → {t : QTy} →
    ComMulti quantumDialect Γ t → CatCrypt.Quantum.QSSAToCircuit.RegAlloc numQ →
    CatCrypt.Quantum.QCircuit.Circuit numQ
  | _, _, .ret _, _ => .empty
  | _, _, .var e body, ra =>
      let (gateOpt, bindQ) := QSSAToVIRCircuit.lowerExpr hpos ra e
      let body' := lowerMultiVIRCom hpos body (ra.extend bindQ)
      match gateOpt with
      | some g => .gate g body'
      | none => body'
  | _, _, .letProj v body, ra =>
      -- Look up the physical qubit the pair-typed parent was bound to,
      -- and extend the allocator twice (one per projection). Both
      -- projections share the parent's slot at this demo layer.
      let pairQ := ra.lookup (QSSAToVIRCircuit.virVarIndex v)
      let ra' := (ra.extend pairQ).extend pairQ
      lowerMultiVIRCom hpos body ra'

/-! ## 3. `lowerVIRCom` ≡ `lowerMultiVIRCom ∘ toMulti`

The trivial-embedding `Com.toMulti` produces no `letProj` cases, so
multi-binder lowering on the embedding equals single-binder lowering. -/

theorem lowerMultiVIRCom_toMulti_eq {numQ : ℕ} (hpos : 0 < numQ) :
    ∀ {Γ : Ctxt quantumDialect} {t : QTy} (c : Com quantumDialect Γ t)
      (ra : CatCrypt.Quantum.QSSAToCircuit.RegAlloc numQ),
      lowerMultiVIRCom hpos c.toMulti ra =
      QSSAToVIRCircuit.lowerVIRCom hpos c ra
  | _, _, .ret _, _ => rfl
  | _, _, .var e body, ra => by
      have ih := lowerMultiVIRCom_toMulti_eq hpos body
        (ra.extend (QSSAToVIRCircuit.lowerExpr hpos ra e).2)
      simp only [Com.toMulti, lowerMultiVIRCom,
        QSSAToVIRCircuit.lowerVIRCom, ih]
      rfl

/-! ## 4. Pair-aware allocator

The demo allocator aliases the two projections of a `letProj` (both go
to the same physical slot). For arbitrary 2-qubit gate sequences this
is incorrect: after `cnot q0 q1` we want the two `letProj` projections
to land on physical slots `q0` and `q1`, not both on `q0`.

`PairAwareAlloc` extends `RegAlloc` with a per-binding "pair-output"
table. Each 2-qubit op (`cnot`, `cz`) records the (control, target)
pair it produced when its result binding is introduced; `letProj`
looks the pair up and extends the allocator with the two distinct
slots. -/

/-- A pair-aware register allocation: ordinary `RegAlloc` plus, for each
    De Bruijn index, the optional `(q1, q2)` pair recorded by an
    upstream 2-qubit op. `letProj` consults this table.

    The default `pairLookup` (used by `identity`) returns the same slot
    for both components — i.e. degrades gracefully to the demo behaviour
    when no 2-qubit op recorded a real pair. -/
structure PairAwareAlloc (numQ : ℕ) where
  /-- Standard `RegAlloc` for single qubits. -/
  ra : CatCrypt.Quantum.QSSAToCircuit.RegAlloc numQ
  /-- Pair-source lookup keyed by De Bruijn index. -/
  pairLookup : ℕ → Fin numQ × Fin numQ

/-- Identity `PairAwareAlloc` on `numQ` qubits: same wire layout as
    `RegAlloc.identity`, and the pair lookup defaults to `(qᵢ, qᵢ)` (so
    in the absence of recorded pair sources, lowering matches the demo
    allocator). -/
def PairAwareAlloc.identity (numQ : ℕ) (hpos : 0 < numQ) :
    PairAwareAlloc numQ where
  ra := CatCrypt.Quantum.QSSAToCircuit.RegAlloc.identity numQ hpos
  pairLookup i :=
    let q := if h : i < numQ then ⟨i, h⟩ else ⟨0, hpos⟩
    (q, q)

/-- Extend a `PairAwareAlloc` with a fresh binding pointing at physical
    qubit `q`. No pair source is recorded (defaults to `(q, q)`). -/
def PairAwareAlloc.extend {numQ : ℕ} (a : PairAwareAlloc numQ) (q : Fin numQ) :
    PairAwareAlloc numQ where
  ra := a.ra.extend q
  pairLookup i := if i = 0 then (q, q) else a.pairLookup (i - 1)

/-- Extend a `PairAwareAlloc` with a fresh binding *that came from a
    2-qubit op*: the binding's `RegAlloc` slot is the gate's first
    output `q1`, and the recorded pair source is `(q1, q2)`. -/
def PairAwareAlloc.extendPair {numQ : ℕ} (a : PairAwareAlloc numQ)
    (q1 q2 : Fin numQ) : PairAwareAlloc numQ where
  ra := a.ra.extend q1
  pairLookup i := if i = 0 then (q1, q2) else a.pairLookup (i - 1)

/-- A *pair-aware* version of `lowerExpr`. For 2-qubit ops (`cnot`,
    `cz`), returns the *pair* of output slots `(q1, q2)` in addition
    to the emitted gate. For 1-qubit / 0-ary ops, returns
    `(gateOpt, q, q)` — both pair components collapse to the single
    output slot, exactly as the demo behaviour. -/
def lowerExprPairAware {numQ : ℕ} (hpos : 0 < numQ)
    {Γ : Ctxt quantumDialect} {t : QTy}
    (a : PairAwareAlloc numQ) (e : Expr quantumDialect Γ t) :
    Option (Gate numQ) × Fin numQ × Fin numQ :=
  match e.op, e.args with
  | .init0, _ => (none, ⟨0, hpos⟩, ⟨0, hpos⟩)
  | .init1, _ => (none, ⟨0, hpos⟩, ⟨0, hpos⟩)
  | .hadamard, .cons v _ =>
      let q := a.ra.lookup (QSSAToVIRCircuit.virVarIndex v); (some (.H q), q, q)
  | .pauliX, .cons v _ =>
      let q := a.ra.lookup (QSSAToVIRCircuit.virVarIndex v); (some (.X q), q, q)
  | .pauliY, .cons v _ =>
      let q := a.ra.lookup (QSSAToVIRCircuit.virVarIndex v); (some (.Y q), q, q)
  | .pauliZ, .cons v _ =>
      let q := a.ra.lookup (QSSAToVIRCircuit.virVarIndex v); (some (.Z q), q, q)
  | .sGate, .cons v _ =>
      let q := a.ra.lookup (QSSAToVIRCircuit.virVarIndex v); (some (.S q), q, q)
  | .tGate, .cons v _ =>
      let q := a.ra.lookup (QSSAToVIRCircuit.virVarIndex v); (some (.T q), q, q)
  | .rz _, .cons v _ =>
      let q := a.ra.lookup (QSSAToVIRCircuit.virVarIndex v); (some (.Rz q 0), q, q)
  | .rzReal θ, .cons v _ =>
      let q := a.ra.lookup (QSSAToVIRCircuit.virVarIndex v); (some (.Rz q θ), q, q)
  | .cnot, .cons v₁ (.cons v₂ _) =>
      let q1 := a.ra.lookup (QSSAToVIRCircuit.virVarIndex v₁)
      let q2 := a.ra.lookup (QSSAToVIRCircuit.virVarIndex v₂)
      (some (.CNOT q1 q2), q1, q2)
  | .cz, .cons v₁ (.cons v₂ _) =>
      let q1 := a.ra.lookup (QSSAToVIRCircuit.virVarIndex v₁)
      let q2 := a.ra.lookup (QSSAToVIRCircuit.virVarIndex v₂)
      (some (.CZ q1 q2), q1, q2)
  | .measure, .cons v _ =>
      let q := a.ra.lookup (QSSAToVIRCircuit.virVarIndex v); (some (.Meas q), q, q)
  | .discard, _ => (none, ⟨0, hpos⟩, ⟨0, hpos⟩)
  | .genericGate _ _, _ => (none, ⟨0, hpos⟩, ⟨0, hpos⟩)
  | .adjoint _, _ => (none, ⟨0, hpos⟩, ⟨0, hpos⟩)
  | .controlled _, _ => (none, ⟨0, hpos⟩, ⟨0, hpos⟩)

/-- Pair-aware multi-binder lowering. Mirrors `lowerMultiVIRCom` for
    the `ret` / `var` / `letProj` constructors but routes the two
    projections of `letProj` to *distinct* physical slots (the ones
    recorded by the upstream 2-qubit op).

    `letProj` binds `body` in context `t₂ :: t₁ :: Γ`:
    * `.here` → second component → physical slot `q2`
    * `.there .here` → first component → physical slot `q1`

    (This matches the `MultiCom.denote` convention: `letProj p body`
    threads the components via
    `(V.extend (proj₁ p)).extend (proj₂ p)` — the second component
    sits on top of the extended valuation, i.e. at `.here`.) -/
def lowerMultiVIRCom_pairAware {numQ : ℕ} (hpos : 0 < numQ) :
    {Γ : Ctxt quantumDialect} → {t : QTy} →
    ComMulti quantumDialect Γ t → PairAwareAlloc numQ →
    CatCrypt.Quantum.QCircuit.Circuit numQ
  | _, _, .ret _, _ => .empty
  | _, _, .var e body, a =>
      let (gateOpt, q1, q2) := lowerExprPairAware hpos a e
      let a' := a.extendPair q1 q2
      let body' := lowerMultiVIRCom_pairAware hpos body a'
      match gateOpt with
      | some g => .gate g body'
      | none => body'
  | _, _, .letProj v body, a =>
      -- Look up the recorded pair source for `v`; extend with q1 then q2
      -- so that `.here` (newest binding) is the second projection (q2)
      -- and `.there .here` is the first projection (q1).
      let (q1, q2) := a.pairLookup (QSSAToVIRCircuit.virVarIndex v)
      let a' := (a.extend q1).extend q2
      lowerMultiVIRCom_pairAware hpos body a'

/-! ## 5. Demonstration: pair-aware vs. demo allocator on a CNOT-then-split

Consider a program that, given two input qubits already in scope (so the
register allocator's identity assignment puts them at *distinct* slots),
CNOTs them, splits the resulting pair, then applies `H` to the first
output and `X` to the second. Under the demo allocator both `H` and `X`
act on the same physical qubit (incorrect aliasing); under the pair-aware
allocator they act on distinct slots. -/

namespace PairAwareDemo

/-- Auxiliary: a 1-qubit Hadamard. -/
def eHadamard {Γ : Ctxt quantumDialect} (v : Ctxt.Var Γ .qubit) :
    Expr quantumDialect Γ .qubit :=
  { op := .hadamard, retTy_eq := rfl, args := .cons v .nil }

/-- Auxiliary: a 1-qubit Pauli-X. -/
def ePauliX {Γ : Ctxt quantumDialect} (v : Ctxt.Var Γ .qubit) :
    Expr quantumDialect Γ .qubit :=
  { op := .pauliX, retTy_eq := rfl, args := .cons v .nil }

/-- Auxiliary: a 2-qubit CNOT. -/
def eCNOT {Γ : Ctxt quantumDialect} (v₁ v₂ : Ctxt.Var Γ .qubit) :
    Expr quantumDialect Γ (.pair .qubit .qubit) :=
  { op := .cnot, retTy_eq := rfl, args := .cons v₁ (.cons v₂ .nil) }

/-- Demo witness program (lives in context `[.qubit, .qubit]` so the
    identity allocator already assigns the two input qubits to distinct
    physical slots, `0` and `1`):

    1. `CNOT q1 q0`  (control = `.there .here` at slot 1, target = `.here` at slot 0).
       Result: pair binding; pair-aware records `(1, 0)`.
    2. `letProj` → split into `(q0', q1')`. With pair-aware:
       `.there .here = q0' = slot 1`, `.here = q1' = slot 0`.
       With demo: both projections → slot 1 (the parent's slot).
    3. `H q0'`. Pair-aware: H on slot 1. Demo: H on slot 1 (both agree
       on this one — they happen to coincide for the *first* projection).
    4. `X q1'`. After the H binding shifts, `q1'` is at `.there .here`.
       Pair-aware: X on slot 0. Demo: X on slot 1 (the aliased projection).
    5. Return the X output. -/
def cnotSplitProg : ComMulti quantumDialect [.qubit, .qubit] .qubit :=
  -- CNOT q1 q0   (Γ = [.qubit, .qubit])
  .var (eCNOT (.there .here) .here) <|
  -- letProj: split pair binding into (q0', q1'); .here = q1', .there .here = q0'.
  .letProj .here <|
  -- H q0'  (q0' at `.there .here`)
  .var (eHadamard (.there .here)) <|
  -- X q1'  (q1' is now at `.there .here` after the H rebinds .here)
  .var (ePauliX (.there .here)) <|
  .ret .here

/-- The identity 2-qubit `PairAwareAlloc`. -/
def pa2 : PairAwareAlloc 2 := PairAwareAlloc.identity 2 (by omega)

/-- The identity 2-qubit `RegAlloc` (for the demo lowering). -/
def ra2 : CatCrypt.Quantum.QSSAToCircuit.RegAlloc 2 :=
  CatCrypt.Quantum.QSSAToCircuit.RegAlloc.identity 2 (by omega)

/-- Under the *demo* allocator, the pair-typed binding sits at slot 1
    (the CNOT's first output) and `letProj` aliases both projections
    onto slot 1. The H on the "first projection" lands on slot 1
    (correct by coincidence) and the X on the "second projection"
    also lands on slot 1 (incorrect aliasing). -/
def cnotSplitProg_demo : Circuit 2 :=
  lowerMultiVIRCom (numQ := 2) (by omega) cnotSplitProg ra2

/-- Demo lowering's exact gate sequence — the X aliases onto slot 1. -/
theorem cnotSplitProg_demo_eq :
    cnotSplitProg_demo =
      .gate (.CNOT 1 0) (.gate (.H 1) (.gate (.X 1) .empty)) := by
  rfl

/-- Demo lowering: 3 gates (CNOT + H + X). -/
theorem cnotSplitProg_demo_gateCount : cnotSplitProg_demo.gateCount = 3 := by rfl

/-- Under the *pair-aware* allocator the CNOT records the pair
    `(1, 0)`, so `letProj` extends to slots `1` (q0') then `0` (q1').
    The trailing H lands on slot 1, the X on slot 0 — qubits are no
    longer aliased. -/
def cnotSplitProg_pairAware : Circuit 2 :=
  lowerMultiVIRCom_pairAware (numQ := 2) (by omega) cnotSplitProg pa2

/-- Pair-aware lowering's exact gate sequence — H on slot 1, X on
    slot 0 (distinct). -/
theorem cnotSplitProg_pairAware_eq :
    cnotSplitProg_pairAware =
      .gate (.CNOT 1 0) (.gate (.H 1) (.gate (.X 0) .empty)) := by
  rfl

/-- Pair-aware lowering: same 3 gates as the demo lowering — but on
    different qubits. The gate count alone does not distinguish them;
    the per-gate qubit indices do. -/
theorem cnotSplitProg_pairAware_gateCount :
    cnotSplitProg_pairAware.gateCount = 3 := by rfl

/-- The two lowerings emit different circuits — the demo path aliases
    the X onto slot `1`; the pair-aware path keeps it at slot `0`. -/
theorem cnotSplitProg_demo_ne_pairAware :
    cnotSplitProg_demo ≠ cnotSplitProg_pairAware := by
  rw [cnotSplitProg_demo_eq, cnotSplitProg_pairAware_eq]
  intro h
  -- Unfold the structural inequality: the X argument differs (1 vs 0).
  injection h with _ h1
  injection h1 with _ h2
  injection h2 with hX _
  -- hX : Gate.X 1 = Gate.X 0
  injection hX with hi
  -- hi : (1 : Fin 2) = 0
  exact absurd hi (by decide)

end PairAwareDemo

/-! ## 6. Structural correctness of the pair-aware lowering

The pair-aware lowering produces a circuit with the same gate count
and same gate-name sequence as the demo lowering — the only difference
is in the qubit indices assigned by the allocator. We formalise this
via `tagSeq`: a list of gate "tags" stripping out the `Fin numQ`
arguments. -/

/-- Gate tag — a coarse classifier ignoring physical qubit indices. -/
inductive GateTag where
  | h | x | y | z | s | t | tdg | cnot | cz | rz | meas
  deriving DecidableEq, Repr

/-- Extract a gate's tag (ignoring `Fin numQ` arguments). -/
def gateTag {numQ : ℕ} : Gate numQ → GateTag
  | .H _ => .h | .X _ => .x | .Y _ => .y | .Z _ => .z
  | .S _ => .s | .T _ => .t | .Tdg _ => .tdg
  | .CNOT _ _ => .cnot | .CZ _ _ => .cz
  | .Rz _ _ => .rz | .Meas _ => .meas

/-- Sequence of gate tags in a `Circuit`. -/
def circuitTagSeq {numQ : ℕ} : Circuit numQ → List GateTag
  | .empty => []
  | .gate g c => gateTag g :: circuitTagSeq c
  | .seq c₁ c₂ => circuitTagSeq c₁ ++ circuitTagSeq c₂

/-- For the demonstration program, the pair-aware lowering preserves
    the demo lowering's gate-name sequence (only qubit indices change).
    Structurally: `[CNOT, H, X]`. -/
theorem cnotSplitProg_tagSeq_eq :
    circuitTagSeq PairAwareDemo.cnotSplitProg_demo =
      circuitTagSeq PairAwareDemo.cnotSplitProg_pairAware := by
  rfl

/-- Explicit gate-tag sequence: `[CNOT, H, X]`. -/
theorem cnotSplitProg_tagSeq_explicit :
    circuitTagSeq PairAwareDemo.cnotSplitProg_pairAware =
      [GateTag.cnot, GateTag.h, GateTag.x] := by
  rfl

end CatCrypt.Crypto.SecureCompilation.VIR.QuantumDialect
