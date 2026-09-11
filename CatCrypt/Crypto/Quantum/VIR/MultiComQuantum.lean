/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.MultiCom
public import CatCrypt.Crypto.SecureCompilation.VIR.QuantumDialect
public import CatCrypt.Crypto.Quantum.VIR.QSSAToVIRCircuit

@[expose] public section

set_option autoImplicit false

/-!
# `MultiCom` setup for `quantumDialect` (Phase 4 #7)

Wires the `PairDialect` typeclass for `quantumDialect` and provides a
multi-binder lowering `lowerMultiVIRCom : ComMulti quantumDialect Γ t →
PairAwareAlloc numQ → Circuit numQ` that mirrors `lowerVIRCom` from
`QSSAToVIRCircuit.lean` and handles the `letProj` case.

A `letProj` splits a pair-typed binding into its two components, and each
component denotes a physical wire — the wire the op that produced the pair
acted on. `RegAlloc` maps a De Bruijn index to a single wire, so it cannot
answer that question for a pair binding. `PairAwareAlloc` carries the extra
table: a `RegAlloc` together with, per De Bruijn index, the two component
wires recorded when the binding was introduced. `lowerExprPairAware` records
`(control, target)` for a 2-qubit op and the binding's own wire twice for
every other op; `PairAwareAlloc.split` is the `letProj` step, and
`PairAwareAlloc.split_lookup` states that the two projection variables it
introduces look up exactly the two recorded wires.

The wire assignment itself is untouched: `lowerExprPairAware` is
`QSSAToVIRCircuit.lowerExpr` paired with the pair-source table, so
`lowerMultiVIRCom_toMulti_eq` relates the multi-binder lowering to the
single-binder `lowerVIRCom` on the embedded `Com` fragment.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.QuantumDialect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Quantum.QCircuit

/-! ## 1. `PairDialect` instance for `quantumDialect` -/

instance : PairDialect quantumDialect where
  pairTy := .pair
  proj₁ := Prod.fst
  proj₂ := Prod.snd

/-! ## 2. The pair-aware register allocation

`RegAlloc` answers "which wire does De Bruijn index `i` denote". A
`letProj` needs "which two wires do the components of the pair at index
`i` denote", which a single-wire answer cannot express.
`PairAwareAlloc` adds that second table. -/

/-- A register allocation together with a pair-source table: for each De
    Bruijn index, the two component wires of the value bound there.

    For a binding produced by a 2-qubit op the pair source is the op's
    `(control, target)`; for every other binding it is the binding's own
    wire in both components. -/
structure PairAwareAlloc (numQ : ℕ) where
  /-- Wire assignment for single qubits. -/
  ra : CatCrypt.Quantum.QSSAToCircuit.RegAlloc numQ
  /-- Component wires of the value at each De Bruijn index. -/
  pairLookup : ℕ → Fin numQ × Fin numQ

/-- Lift a `RegAlloc` to a `PairAwareAlloc` with no recorded pair source:
    the components of the value at index `i` both sit on the wire `i`
    itself denotes. This is the entry point for a program whose free
    variables carry no pair provenance. -/
def PairAwareAlloc.ofRegAlloc {numQ : ℕ}
    (ra : CatCrypt.Quantum.QSSAToCircuit.RegAlloc numQ) : PairAwareAlloc numQ where
  ra := ra
  pairLookup i := (ra.lookup i, ra.lookup i)

/-- Identity `PairAwareAlloc` on `numQ` qubits: variable `i` occupies
    physical qubit `i`, with no recorded pair source. -/
def PairAwareAlloc.identity (numQ : ℕ) (hpos : 0 < numQ) :
    PairAwareAlloc numQ :=
  PairAwareAlloc.ofRegAlloc
    (CatCrypt.Quantum.QSSAToCircuit.RegAlloc.identity numQ hpos)

/-- Introduce a binding whose wire assignment is `ra'` and whose pair
    source is `(q1, q2)`; the older bindings shift by one. -/
def PairAwareAlloc.record {numQ : ℕ} (a : PairAwareAlloc numQ)
    (ra' : CatCrypt.Quantum.QSSAToCircuit.RegAlloc numQ) (q1 q2 : Fin numQ) :
    PairAwareAlloc numQ where
  ra := ra'
  pairLookup i := if i = 0 then (q1, q2) else a.pairLookup (i - 1)

/-- Introduce a binding on physical qubit `q` with no pair source. -/
def PairAwareAlloc.extend {numQ : ℕ} (a : PairAwareAlloc numQ) (q : Fin numQ) :
    PairAwareAlloc numQ :=
  a.record (a.ra.extend q) q q

/-- The `letProj` step: split the binding at De Bruijn index `i` into its
    two recorded component wires. The first component is bound first and
    the second on top of it, matching `ComMulti.letProj`'s context
    `t₂ :: t₁ :: Γ` — so `.there .here` is the first component and
    `.here` the second. -/
def PairAwareAlloc.split {numQ : ℕ} (a : PairAwareAlloc numQ) (i : ℕ) :
    PairAwareAlloc numQ :=
  (a.extend (a.pairLookup i).1).extend (a.pairLookup i).2

/-- The two variables a `split` introduces look up the two component
    wires recorded for the split binding: De Bruijn index `1`
    (`.there .here`, the first component) takes the first recorded wire
    and index `0` (`.here`, the second component) the second. -/
theorem PairAwareAlloc.split_lookup {numQ : ℕ} (a : PairAwareAlloc numQ) (i : ℕ) :
    ((a.split i).ra.lookup 1, (a.split i).ra.lookup 0) = a.pairLookup i := rfl

/-! ## 3. Expression lowering with pair-source recording

`lowerExprPairAware` is `QSSAToVIRCircuit.lowerExpr` — same gate, same
wire assignment — carrying the pair source of the binding it introduces
alongside. -/

/-- The two component wires of the value an expression binds: the
    `(control, target)` pair of a 2-qubit op, and the binding's own wire
    twice for every other op. -/
def exprPairSource {numQ : ℕ} (hpos : 0 < numQ) {Γ : Ctxt quantumDialect}
    {t : QTy} (a : PairAwareAlloc numQ) (e : Expr quantumDialect Γ t) :
    Fin numQ × Fin numQ :=
  let ra' := (QSSAToVIRCircuit.lowerExpr hpos a.ra e).2
  match e.op, e.args with
  | .cnot, .cons _ (.cons v₂ _) =>
      (ra'.lookup 0, a.ra.lookup (QSSAToVIRCircuit.virVarIndex v₂))
  | .cz, .cons _ (.cons v₂ _) =>
      (ra'.lookup 0, a.ra.lookup (QSSAToVIRCircuit.virVarIndex v₂))
  | _, _ => (ra'.lookup 0, ra'.lookup 0)

/-- Gate emission and allocator update for a single dialect expression:
    the gate and the wire assignment are `QSSAToVIRCircuit.lowerExpr`'s,
    and the new binding records `exprPairSource` as its pair source. -/
def lowerExprPairAware {numQ : ℕ} (hpos : 0 < numQ)
    {Γ : Ctxt quantumDialect} {t : QTy}
    (a : PairAwareAlloc numQ) (e : Expr quantumDialect Γ t) :
    Option (Gate numQ) × PairAwareAlloc numQ :=
  let (gateOpt, ra') := QSSAToVIRCircuit.lowerExpr hpos a.ra e
  let p := exprPairSource hpos a e
  (gateOpt, a.record ra' p.1 p.2)

/-- The gate emitted is the one `QSSAToVIRCircuit.lowerExpr` emits. -/
theorem lowerExprPairAware_gate {numQ : ℕ} (hpos : 0 < numQ)
    {Γ : Ctxt quantumDialect} {t : QTy}
    (a : PairAwareAlloc numQ) (e : Expr quantumDialect Γ t) :
    (lowerExprPairAware hpos a e).1 =
      (QSSAToVIRCircuit.lowerExpr hpos a.ra e).1 := rfl

/-- The wire assignment produced is `QSSAToVIRCircuit.lowerExpr`'s. -/
theorem lowerExprPairAware_ra {numQ : ℕ} (hpos : 0 < numQ)
    {Γ : Ctxt quantumDialect} {t : QTy}
    (a : PairAwareAlloc numQ) (e : Expr quantumDialect Γ t) :
    (lowerExprPairAware hpos a e).2.ra =
      (QSSAToVIRCircuit.lowerExpr hpos a.ra e).2 := rfl

/-! ## 4. Multi-binder lowering -/

/-- Lowering of a `ComMulti quantumDialect` to a `Circuit numQ`.

    Mirrors `lowerVIRCom` for the `ret` / `var` cases; `letProj` routes
    each of the two projections to the wire its component of the parent
    binding occupies, via `PairAwareAlloc.split`. -/
def lowerMultiVIRCom {numQ : ℕ} (hpos : 0 < numQ) :
    {Γ : Ctxt quantumDialect} → {t : QTy} →
    ComMulti quantumDialect Γ t → PairAwareAlloc numQ →
    CatCrypt.Quantum.QCircuit.Circuit numQ
  | _, _, .ret _, _ => .empty
  | _, _, .var e body, a =>
      let (gateOpt, a') := lowerExprPairAware hpos a e
      let body' := lowerMultiVIRCom hpos body a'
      match gateOpt with
      | some g => .gate g body'
      | none => body'
  | _, _, .letProj v body, a =>
      lowerMultiVIRCom hpos body (a.split (QSSAToVIRCircuit.virVarIndex v))

/-! ## 5. `lowerVIRCom` ≡ `lowerMultiVIRCom ∘ toMulti`

The trivial embedding `Com.toMulti` produces no `letProj` cases, so
multi-binder lowering on the embedding equals single-binder lowering
under the underlying `RegAlloc`. -/

theorem lowerMultiVIRCom_toMulti_eq {numQ : ℕ} (hpos : 0 < numQ) :
    ∀ {Γ : Ctxt quantumDialect} {t : QTy} (c : Com quantumDialect Γ t)
      (a : PairAwareAlloc numQ),
      lowerMultiVIRCom hpos c.toMulti a =
      QSSAToVIRCircuit.lowerVIRCom hpos c a.ra
  | _, _, .ret _, _ => rfl
  | _, _, .var e body, a => by
      have ih := lowerMultiVIRCom_toMulti_eq hpos body
        (lowerExprPairAware hpos a e).2
      simp only [Com.toMulti, lowerMultiVIRCom,
        QSSAToVIRCircuit.lowerVIRCom, lowerExprPairAware_ra, ih]
      rfl

/-! ## 6. Correspondence at a `letProj`

`PairAwareAlloc.split_lookup` states the property at the allocator
level. Composed with the pair source a 2-qubit op records, it says that
the wires the two projection variables denote are exactly the two wires
the emitted gate acts on. -/

/-- For a `cnot` binding split immediately by `letProj`, the emitted gate
    acts on the two wires the body's projection variables denote: the
    control wire is the one `.there .here` (the first component, De Bruijn
    index `1`) looks up, and the target wire the one `.here` (the second
    component, index `0`) looks up. -/
theorem lowerMultiVIRCom_cnot_letProj {numQ : ℕ} (hpos : 0 < numQ)
    {Γ : Ctxt quantumDialect} {s : QTy}
    (v₁ v₂ : Ctxt.Var (d := quantumDialect) Γ .qubit)
    (body : ComMulti quantumDialect
      (.qubit :: .qubit :: QTy.pair .qubit .qubit :: Γ) s)
    (a : PairAwareAlloc numQ) :
    let e : Expr quantumDialect Γ (QTy.pair .qubit .qubit) :=
      { op := .cnot, retTy_eq := rfl, args := .cons v₁ (.cons v₂ .nil) }
    let a' := ((lowerExprPairAware hpos a e).2).split 0
    lowerMultiVIRCom hpos (.var e (.letProj .here body)) a =
      .gate (.CNOT (a'.ra.lookup 1) (a'.ra.lookup 0))
        (lowerMultiVIRCom hpos body a') := rfl

/-- The same statement for `cz`. -/
theorem lowerMultiVIRCom_cz_letProj {numQ : ℕ} (hpos : 0 < numQ)
    {Γ : Ctxt quantumDialect} {s : QTy}
    (v₁ v₂ : Ctxt.Var (d := quantumDialect) Γ .qubit)
    (body : ComMulti quantumDialect
      (.qubit :: .qubit :: QTy.pair .qubit .qubit :: Γ) s)
    (a : PairAwareAlloc numQ) :
    let e : Expr quantumDialect Γ (QTy.pair .qubit .qubit) :=
      { op := .cz, retTy_eq := rfl, args := .cons v₁ (.cons v₂ .nil) }
    let a' := ((lowerExprPairAware hpos a e).2).split 0
    lowerMultiVIRCom hpos (.var e (.letProj .here body)) a =
      .gate (.CZ (a'.ra.lookup 1) (a'.ra.lookup 0))
        (lowerMultiVIRCom hpos body a') := rfl

/-! ## 7. Demonstration: a CNOT, split, then one gate per output

A program that CNOTs two input qubits already in scope, splits the
resulting pair, and applies `H` to the first output and `X` to the
second. The `H` lands on the CNOT's control wire and the `X` on its
target wire. -/

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

/-- Witness program in context `[.qubit, .qubit]`, so the identity
    allocator already assigns the two input qubits to distinct physical
    slots `0` and `1`:

    1. `CNOT q1 q0` — control `.there .here` (slot 1), target `.here`
       (slot 0). The pair binding records `(1, 0)`.
    2. `letProj` splits the pair: `.there .here` is the first component
       (slot 1), `.here` the second (slot 0).
    3. `H` on the first component, i.e. slot 1.
    4. `X` on the second component; after the `H` binding shifts the
       context it sits at `.there .here`, i.e. slot 0.
    5. Return the `X` output. -/
def cnotSplitProg : ComMulti quantumDialect [.qubit, .qubit] .qubit :=
  -- CNOT q1 q0   (Γ = [.qubit, .qubit])
  .var (eCNOT (.there .here) .here) <|
  -- letProj: .there .here = first component, .here = second component.
  .letProj .here <|
  -- H on the first component (at `.there .here`)
  .var (eHadamard (.there .here)) <|
  -- X on the second component (at `.there .here` after the H rebinds .here)
  .var (ePauliX (.there .here)) <|
  .ret .here

/-- The identity 2-qubit `PairAwareAlloc`. -/
def pa2 : PairAwareAlloc 2 := PairAwareAlloc.identity 2 (by omega)

/-- The witness program lowered from the identity `PairAwareAlloc`. -/
def cnotSplitProg_demo : Circuit 2 :=
  lowerMultiVIRCom (numQ := 2) (by omega) cnotSplitProg pa2

/-- Exact gate sequence: `CNOT 1 0`, then `H` on the control wire `1` and
    `X` on the target wire `0`. -/
theorem cnotSplitProg_demo_eq :
    cnotSplitProg_demo =
      .gate (.CNOT 1 0) (.gate (.H 1) (.gate (.X 0) .empty)) := by
  rfl

/-- Three gates: CNOT + H + X. -/
theorem cnotSplitProg_demo_gateCount : cnotSplitProg_demo.gateCount = 3 := by rfl

end PairAwareDemo

/-! ## 8. Gate-tag sequences

`circuitTagSeq` records a circuit's gate names with the physical qubit
indices erased, which separates a lowering's gate schedule from its wire
assignment. -/

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

/-- Gate-tag sequence of the demonstration program: `[CNOT, H, X]`. -/
theorem cnotSplitProg_tagSeq_explicit :
    circuitTagSeq PairAwareDemo.cnotSplitProg_demo =
      [GateTag.cnot, GateTag.h, GateTag.x] := by
  rfl

end CatCrypt.Crypto.SecureCompilation.VIR.QuantumDialect
