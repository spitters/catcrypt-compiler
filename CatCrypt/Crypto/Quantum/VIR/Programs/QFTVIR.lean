/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Quantum.VIR.QSSAToVIRCircuit
public import CatCrypt.Crypto.Quantum.VIR.MultiComQuantum
public import CatCrypt.Quantum.Benchmark.Suite

@[expose] public section

set_option autoImplicit false

/-!
# Phase 3 (scale test): Quantum Fourier Transform (n=2) ported to `Com quantumDialect`

Validates the Phase-3 cleanliness claim on a non-toy circuit: the 2-qubit
QFT. The reference matrix-level QFT lives at
`CatCrypt/Quantum/Programs/QFT.lean` (~191 LoC); the benchmark suite
exposes the gate-decomposed form as `qft2 : Circuit 2` with 6 gates
(`H, Rz(π/2), H, CNOT, CNOT, CNOT` — the last three implement SWAP).

We encode the QFT in two forms:

1. **QSProg form** — `qftQSProg` in A-normal form, with `letInit` for
   init, `letQ` for `H` / `Rz`, `letQ2` for the three CNOTs implementing
   the trailing SWAP.
2. **VIR form** — `qftVIR` as `Com quantumDialect [] (.pair .qubit .qubit)`.

The three equivalence theorems mirror the Deutsch-Jozsa pattern:

* `qftVIR_eq_toVIRCom` — the VIR form equals the Phase-2 translation
  `toVIRCom` of the QSProg form. **Proof: `rfl`.**
* `qftVIR_lowerVIRCom_gateCount` — `lowerVIRCom`'s gate count equals
  the expected 4 gates (the non-SWAP prefix of `qft2`).
* `qftVIR_lowerVIRCom_eq_qft2Stub` — the lowered VIR equals the
  4-gate `qft2` benchmark prefix, with the exact `π/2` angle and the
  two QFT wires on distinct physical qubits.

## The `rz` angle

The dialect carries two `Rz` constructors: `QOp.rz : Float → QOp`
(computable) and `QOp.rzReal : ℝ → QOp` (exact). The Phase-2 bridge
`mkUnitary1Expr` routes `QSProg.QOp.rz θ` to `QOp.rzReal θ` with no
conversion, and `lowerExpr` lowers `rzReal θ` to `Gate.Rz q θ`. For
QFT-2 this means `lowerVIRCom (toVIRCom qftQSProg) ra2` emits
`Rz 1 (Real.pi / 2)`, the same gate `qft2 : Circuit 2` carries.
`QOpCircuitFriendly` admits `.rz`, so `lowerVIRCom_toVIRCom_eq`
applies to QFT.

`qftVIR` is the single-binder encoding and covers the 4-gate
`H, Rz, H, CNOT` prefix; the trailing 3-CNOT SWAP needs a pair
destructor, which §9's `ComMulti` encoding `qftVIRFull` supplies.

## Scaling snapshot

* QFT-2 matrix-level (`Quantum/Programs/QFT.lean`): 190 LoC, three
  `set_option maxHeartbeats 3200000`–`6400000` blocks (for the
  `qftMatrix * qftMatrixᴴ = 1` unitarity proof and `qft²` bit-reversal).
* QFT-2 VIR port (this file): no `maxHeartbeats` override, `rfl` and
  `decide` proofs throughout.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.Programs.QFTVIR

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.QuantumDialect
open CatCrypt.Crypto.SecureCompilation.VIR.QSSAToVIR
open CatCrypt.Crypto.SecureCompilation.VIR.QSSAToVIRCircuit
open CatCrypt.Quantum CatCrypt.Quantum.QSSAToCircuit
open CatCrypt.Quantum.QCircuit CatCrypt.Quantum.QuantumSSA
open CatCrypt.Quantum.Benchmark.Suite

noncomputable section

/-! ## 1. QFT-2 as `QSProg`

The 2-qubit QFT decomposition (`qft2 : Circuit 2`):
```
H  q0
Rz q1, π/2
H  q1
CNOT q0 q1
CNOT q1 q0
CNOT q0 q1   -- last three = SWAP via 3 CNOTs
```

In A-normal form, `q0` and `q1` are introduced by two `letInit`s; each
gate then binds a fresh variable. -/

/-- QFT-2 (no-SWAP variant) as a `QSProg`. The `Rz` angle is
    `Real.pi / 2` (the canonical QFT-2 phase). As of 2026-05-14 the
    Phase-2 bridge preserves the exact angle via `QOp.rzReal`.

    **Demo limitation**: the canonical 6-gate `qft2 : Circuit 2` from
    `Quantum/Benchmark/Suite.lean` ends with three successive CNOTs
    implementing a final SWAP. The current dialect (Phase 2) returns a
    `pair qubit qubit` from each 2-qubit gate, with no pair destructor,
    so we cannot chain 2-qubit gates. This is the same limitation
    documented in `DeutschJozsaVIR` and `GroverVIR` (which truncate
    their circuits before the final 2-qubit chains). The 4-gate
    `H, Rz, H, CNOT` form below is the maximal QFT-2 prefix expressible
    in the current dialect; the SWAP completion is a Phase-4 deliverable
    (multi-result binders / pair destructors). -/
def qftQSProg : QSProg [] (.pair .qubit .qubit) :=
  -- q0 = init0; q1 = init0
  .letInit .init0 <|
  .letInit .init0 <|
  -- H q0
  .letQ .hadamard (.there .here) <|
  -- Rz(π/2) on q1
  .letQ (.rz (Real.pi / 2)) (.there .here) <|
  -- H q1
  .letQ .hadamard (.here) <|
  -- CNOT q0 q1 (pair result returned; can't chain further 2-qubit gates
  -- without a pair destructor — Phase 4)
  .letQ2 .cnot (.there (.there .here)) (.here) <|
  .ret .here

theorem qftQSProg_isMeasFree : qftQSProg.isMeasFree := by
  unfold qftQSProg
  simp [QSProg.isMeasFree]

/-! ## 2. QFT-2 as `Com quantumDialect`

Hand-written VIR encoding. Each line corresponds 1:1 to a QSProg line. -/

/-- 0-ary init0 expression. -/
def eInit0 (Γ : Ctxt quantumDialect) : Expr quantumDialect Γ .qubit :=
  { op := .init0, retTy_eq := rfl, args := .nil }

/-- 1-qubit Hadamard expression. -/
def eHadamard {Γ : Ctxt quantumDialect} (v : Ctxt.Var Γ .qubit) :
    Expr quantumDialect Γ .qubit :=
  { op := .hadamard, retTy_eq := rfl, args := .cons v .nil }

/-- 1-qubit `Rz(θ)` expression. The dialect's legacy `Rz` carries `Float`. -/
def eRz {Γ : Ctxt quantumDialect} (θ : Float) (v : Ctxt.Var Γ .qubit) :
    Expr quantumDialect Γ .qubit :=
  { op := .rz θ, retTy_eq := rfl, args := .cons v .nil }

/-- 1-qubit `Rz(θ)` expression with an exact ℝ angle (2026-05-14). -/
def eRzReal {Γ : Ctxt quantumDialect} (θ : ℝ) (v : Ctxt.Var Γ .qubit) :
    Expr quantumDialect Γ .qubit :=
  { op := .rzReal θ, retTy_eq := rfl, args := .cons v .nil }

/-- 2-qubit CNOT expression. -/
def eCNOT {Γ : Ctxt quantumDialect} (v₁ v₂ : Ctxt.Var Γ .qubit) :
    Expr quantumDialect Γ (.pair .qubit .qubit) :=
  { op := .cnot, retTy_eq := rfl, args := .cons v₁ (.cons v₂ .nil) }

/-- QFT-2 (no-SWAP variant) as a `Com quantumDialect`. Uses the exact-ℝ
    `eRzReal` (2026-05-14) so the `Rz` angle `Real.pi / 2` survives the
    `toVIRCom` translation unchanged. -/
def qftVIR : Com quantumDialect [] (.pair .qubit .qubit) :=
  .var (eInit0 _) <|
  .var (eInit0 _) <|
  .var (eHadamard (.there .here)) <|
  .var (eRzReal (Real.pi / 2) (.there .here)) <|
  .var (eHadamard (.here)) <|
  .var (eCNOT (.there (.there .here)) (.here)) <|
  .ret .here

/-! ## 3. The VIR encoding equals `toVIRCom` of the QSProg encoding -/

/-- The hand-written VIR encoding agrees with the Phase-2 translation. -/
theorem qftVIR_eq_toVIRCom :
    toVIRCom qftQSProg = some qftVIR := by
  rfl

/-! ## 4. Gate count of the lowered circuit -/

/-- Identity register allocator on 2 qubits. -/
def ra2 : RegAlloc 2 := RegAlloc.identity 2 (by omega)

/-- Identity pair-aware register allocator on 2 qubits, the allocator the
    multi-binder lowering of §9 runs under. -/
def pa2 : QuantumDialect.PairAwareAlloc 2 :=
  QuantumDialect.PairAwareAlloc.identity 2 (by omega)

/-- The lowered VIR-side QFT (no-SWAP variant) has 4 gates: 2× H, 1× Rz, 1× CNOT.
    The full 6-gate `qft2` adds two more CNOTs to complete the SWAP — out
    of scope until Phase 4 multi-result binders land. -/
theorem qftVIR_lowerVIRCom_gateCount :
    (lowerVIRCom (numQ := 2) (by omega) qftVIR ra2).gateCount = 4 := by
  rfl

/-! ## 5. Equivalence with the `qft2` prefix

`qft2Stub` is the 4-gate no-SWAP prefix of the benchmark `qft2`, and
the VIR-side lowering equals it gate for gate. -/

/-- The 4-gate no-SWAP prefix of the benchmark `qft2`, gate for gate:
    `H 0`, `Rz 1 (π/2)`, `H 1`, `CNOT 0 1`. The two `letInit` bindings
    claim distinct physical qubits (`RegAlloc.allocFresh`), so the two
    QFT wires stay separate and the angle is the exact `Real.pi / 2`. -/
def qft2Stub : Circuit 2 :=
  .gate (.H 0)
  (.gate (.Rz 1 (Real.pi / 2))
  (.gate (.H 1)
  (.gate (.CNOT 0 1)
  .empty)))

theorem qft2Stub_gateCount : qft2Stub.gateCount = 4 := by rfl

/-- The lowered VIR-side QFT equals `qft2Stub` exactly. -/
theorem qftVIR_lowerVIRCom_eq_qft2Stub :
    lowerVIRCom (numQ := 2) (by omega) qftVIR ra2 = qft2Stub := by
  rfl

/-! ## 6. Denotation equivalence

The "real semantics" of `qftVIR` equals the `unitaryDenote` of `qft2Stub`
— `rfl`-level by definition of `Com.realDenoteQComp`. -/

/-- VIR real-denotation equals `unitaryDenote` of the stub circuit. -/
theorem qftVIR_realDenote_eq_qft2Stub :
    Com.realDenoteQComp (numQ := 2) (by omega) qftVIR ra2 =
    GateUnitarity.unitaryDenote qft2Stub := by
  show GateUnitarity.unitaryDenote (lowerVIRCom (numQ := 2) (by omega) qftVIR ra2)
       = GateUnitarity.unitaryDenote qft2Stub
  rw [qftVIR_lowerVIRCom_eq_qft2Stub]

/-! ## 7. QSProg side: `lowerProg` gate count

For the QSProg encoding, `lowerProg` retains the original `Rz` angle.
The gate count still matches. -/

/-- The QSProg-side lowering also produces 4 gates. -/
theorem qftQSProg_lowerProg_gateCount :
    (lowerProg (Γ := []) (β := .pair .qubit .qubit) 2 (by omega)
      (RegAlloc.identity 2 (by omega))
      qftQSProg qftQSProg_isMeasFree).gateCount = 4 := by
  rfl

/-! ## 8. Scaling snapshot

| Metric                       | Matrix (`Quantum/Programs/QFT.lean`) | VIR (this file)            |
|------------------------------|--------------------------------------|----------------------------|
| LoC                          | 191                                  | ~120 (definitions + 3 thms)|
| `maxHeartbeats` overrides    | 3× (3.2M, 3.2M, 6.4M)                | **0**                      |
| Proof style                  | `ext i j; fin_cases ...; complex_entry_tac` hammers | `rfl` / `decide` |
| Gate count check             | N/A (matrix-level only)              | `decide`, instant          |
| Real-denotation equivalence  | N/A (matrix is intrinsic semantics)  | `rfl` after definitional unfold |

The equivalence target `qft2Stub` carries the exact `Real.pi / 2`
angle. The SWAP completion (3 trailing CNOTs) is covered by the
`ComMulti` encoding of Section 9, via the `letProj` pair destructor. -/

/-! ## 9. Full QFT-2 (SWAP completion) via `ComMulti.letProj`

With the multi-binder `ComMulti` (Phase 4 #7, file `VIR/MultiCom.lean`),
the canonical 6-gate QFT-2 — including its trailing 3-CNOT SWAP — is
expressible directly. Each 2-qubit gate emits a `pair qubit qubit`
result, and `letProj` splits the pair into two `qubit` bindings, each on
the wire its component of the pair occupies — the gate's control line for
the first component and its target line for the second. The lowering
runs under `QuantumDialect.PairAwareAlloc`, which carries that record;
`QuantumDialect.lowerMultiVIRCom_cnot_letProj` states the correspondence
in general. -/

/-- Full 6-gate QFT-2 as a `ComMulti quantumDialect`.

    Layout of bindings (newest at the head). After the four prefix gates
    we have the context

        [q1_h, q1_rz, q0_h, q1_init, q0_init]

    (`q0_init`, `q0_h` are old `q0`; `q1_init`, `q1_rz`, `q1_h` are old
    `q1`). The first CNOT takes the latest `q0` (here: `q0_h`, three
    deep) and the latest `q1` (here: `q1_h`, head of context) and
    returns a pair. Each pair is split by a `letProj` immediately after
    its gate; `.there .here` is the first component (the gate's control
    line) and `.here` the second (its target line). The SWAP triple
    alternates control and target, so which of the two variables carries
    the `q0` line alternates with it.

    The final return packs the two SWAP-completed qubits as a pair so
    the program has the same return type as `qftVIR`. -/
def qftVIRFull : ComMulti quantumDialect [] (.pair .qubit .qubit) :=
  -- q0_init, q1_init
  .var (eInit0 _) <|
  .var (eInit0 _) <|
  -- q0_h := H q0_init
  .var (eHadamard (.there .here)) <|
  -- q1_rz := Rz(π/2) q1_init
  .var (eRzReal (Real.pi / 2) (.there .here)) <|
  -- q1_h := H q1_rz
  .var (eHadamard (.here)) <|
  -- p1 := CNOT q0_h q1_h     (Γ = [q1_h, q1_rz, q0_h, q1_init, q0_init])
  --                          (q0_h at `.there (.there .here)`,
  --                           q1_h at `.here`)
  .var (eCNOT (.there (.there .here)) .here) <|
  -- p1 : pair qubit qubit at `.here`; split into (q0_1, q1_1), the
  -- control and target lines of p1.
  .letProj .here <|
  -- Γ extends to [q1_1, q0_1, p1, q1_h, q1_rz, q0_h, q1_init, q0_init]:
  -- q0_1 (first component) at `.there .here`, q1_1 (second) at `.here`.
  -- p2 := CNOT q1_1 q0_1
  .var (eCNOT .here (.there .here)) <|
  -- p2 splits into (q1_2, q0_2), its control and target lines, so Γ
  -- extends to [q0_2, q1_2, p2, q1_1, q0_1, p1, q1_h, q1_rz, q0_h,
  -- q1_init, q0_init]: q1_2 (first component) at `.there .here`,
  -- q0_2 (second) at `.here`.
  .letProj .here <|
  -- p3 := CNOT q0_2 q1_2
  .var (eCNOT .here (.there .here)) <|
  -- Return p3 (already a `pair qubit qubit`).
  .ret .here

/-- The full QFT-2 with SWAP completion: the prefix `H 0`,
    `Rz 1 (π/2)`, `H 1` followed by the CNOT triple `CNOT 0 1`,
    `CNOT 1 0`, `CNOT 0 1` that implements the final SWAP.

    Gate for gate this is the benchmark circuit
    `Quantum.Benchmark.Suite.qft2`, which is written independently of
    this lowering (see `qft2FullStub_eq_qft2`). -/
def qft2FullStub : Circuit 2 :=
  .gate (.H 0)
  (.gate (.Rz 1 (Real.pi / 2))
  (.gate (.H 1)
  (.gate (.CNOT 0 1)
  (.gate (.CNOT 1 0)
  (.gate (.CNOT 0 1)
  .empty)))))

theorem qft2FullStub_gateCount : qft2FullStub.gateCount = 6 := by rfl

/-- The SWAP-completed stub is the benchmark QFT-2 circuit. -/
theorem qft2FullStub_eq_qft2 : qft2FullStub = qft2 := by rfl

/-- The full VIR-side QFT (multi-binder form, SWAP included) lowers to
    the 6-gate stub. -/
theorem qftVIRFull_lowerMultiVIRCom_eq_qft2FullStub :
    QuantumDialect.lowerMultiVIRCom (numQ := 2) (by omega) qftVIRFull pa2 =
    qft2FullStub := by
  rfl

/-- Gate count of the full QFT-2: 6 = 3 (`H`, `Rz`, `H`) + 3 (the
    CNOT triple implementing SWAP), as in the canonical
    decomposition. -/
theorem qftVIRFull_lowerMultiVIRCom_gateCount :
    (QuantumDialect.lowerMultiVIRCom (numQ := 2) (by omega) qftVIRFull pa2).gateCount
      = 6 := by
  rfl

/-- Real `QComp` semantics of the full QFT-2: `unitaryDenote` of the
    SWAP-completed stub. -/
theorem qftVIRFull_realDenote_eq_qft2FullStub :
    GateUnitarity.unitaryDenote
        (QuantumDialect.lowerMultiVIRCom (numQ := 2) (by omega) qftVIRFull pa2) =
    GateUnitarity.unitaryDenote qft2FullStub := by
  rw [qftVIRFull_lowerMultiVIRCom_eq_qft2FullStub]

/-! Sanity tie-in: `qftVIR` embedded via `Com.toMulti` and lowered through the
multi-binder path agrees with the original single-binder lowering. -/

theorem qftVIR_toMulti_lowerMultiVIRCom_eq :
    QuantumDialect.lowerMultiVIRCom (numQ := 2) (by omega) qftVIR.toMulti pa2 =
    lowerVIRCom (numQ := 2) (by omega) qftVIR ra2 :=
  QuantumDialect.lowerMultiVIRCom_toMulti_eq (by omega) qftVIR pa2

end

end CatCrypt.Crypto.SecureCompilation.VIR.Programs.QFTVIR
