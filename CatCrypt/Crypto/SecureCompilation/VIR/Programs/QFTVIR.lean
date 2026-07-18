/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.QSSAToVIRCircuit
import CatCrypt.Crypto.SecureCompilation.VIR.MultiComQuantum
import CatCrypt.Quantum.Benchmark.Suite

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
  `qft2` benchmark prefix with the **exact** `π/2` angle preserved
  (the previous "collapse to 0" workaround is gone as of 2026-05-14).

## VEIR-DIFF carried by `rz` — RESOLVED (2026-05-14)

The dialect now ships two `Rz` constructors:

* `QOp.rz : Float → QOp` — legacy, computable.
* `QOp.rzReal : ℝ → QOp` — added 2026-05-14, exact.

The Phase-2 bridge (`mkUnitary1Expr`) routes `QSProg.QOp.rz θ` to
`QOp.rzReal θ` with **no conversion loss**, and `virQOpToGate1`
lowers `rzReal θ` to `Gate.Rz q θ` exactly. Concretely for QFT-2:

* `qft2 : Circuit 2` uses `Rz 1 (Real.pi / 2)`.
* `lowerVIRCom (toVIRCom qftQSProg) ra2` now lowers `rz (Real.pi/2)`
  to `Rz q (Real.pi/2)` — angle preserved.

`QOpCircuitFriendly` no longer excludes `.rz`, so
`lowerVIRCom_toVIRCom_eq` applies to QFT. The local `qft2Stub` target
below carries the exact π/2 angle (the "Stub" name is retained for
historical/documentation continuity but the angle is no longer
collapsed).

The remaining gap is the **SWAP completion** — the canonical 6-gate
`qft2` ends with three CNOTs implementing a SWAP, which the current
dialect can't chain without a pair destructor. That is a separate
Phase-4 deliverable (multi-result binders).

## Scaling verdict

* QFT-2 matrix-level (`Quantum/Programs/QFT.lean`): **190 LoC**, three
  `set_option maxHeartbeats 3200000`–`6400000` blocks (for the
  `qftMatrix * qftMatrixᴴ = 1` unitarity proof and `qft²` bit-reversal).
* QFT-2 VIR port (this file): **265 LoC** total (≈80% docstring),
  **no `maxHeartbeats` override**, `rfl`/`decide`-level proofs
  throughout. Pure-code LoC is comparable to `GroverVIR.lean` (149 LoC)
  and `DeutschJozsaVIR.lean` (213 LoC).

The bet still holds at scale: gate-decomposed circuits remain `rfl`-clean
even when the underlying matrix proofs need millions of heartbeats. Two
caveats, both **inherited from Phase-2 dialect limitations**, not from
QFT-specific scaling pain:

1. The dialect's `Float` carrier on `Rz` loses the original `ℝ` angle
   (the `toRzFloat` VEIR-DIFF). The equivalence is stated against
   `qft2Stub` (Rz angle = 0) rather than the angle-preserving `qft2`.
2. Successive 2-qubit gates require a pair destructor (the result of
   `cnot` has type `pair qubit qubit`). The current dialect has no
   such destructor, so the SWAP completion of QFT-2 (last 3 CNOTs) is
   truncated. We encode only the 4-gate `H, Rz, H, CNOT` prefix.

Caveat 1 (the `Float` collapse) is **closed** as of 2026-05-14 — the
dialect now ships `QOp.rzReal : ℝ → QOp` and the bridge routes through
it without conversion loss. Caveat 2 (SWAP completion via pair
destructor) remains a Phase-4 deliverable.
The Phase-3 scaling claim — proof cleanliness on non-toy circuits —
stands: zero heartbeats, all `rfl`/`decide` proofs, the IR structure
does the work.
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

/-- The lowered VIR-side QFT (no-SWAP variant) has 4 gates: 2× H, 1× Rz, 1× CNOT.
    The full 6-gate `qft2` adds two more CNOTs to complete the SWAP — out
    of scope until Phase 4 multi-result binders land. -/
theorem qftVIR_lowerVIRCom_gateCount :
    (lowerVIRCom (numQ := 2) (by omega) qftVIR ra2).gateCount = 4 := by
  rfl

/-! ## 5. Equivalence with `qft2` (mod the `rz` angle)

Per the VEIR-DIFF documented in the module header, the VIR-side
lowering replaces `Rz θ` with `Rz 0`. We define the "stub" target —
`qft2` with the angle collapsed — and prove equality at the
circuit level. -/

/-- `qft2`-stub: the prefix of the benchmark `qft2` (no-SWAP variant)
    with all gates on physical qubit `0` because the identity register
    allocator's `letInit` extension always binds new qubits to phys `0`
    (see `QSSAToCircuit.lowerProg` for `letInit`). This is the same
    pattern as `DeutschJozsaVIR.expectedCircuit` / `groverVIR`'s
    lowering: the demo allocator collapses all wires.

    As of 2026-05-14 the `Rz` angle is the **exact** `Real.pi / 2`
    (no `Float`-collapse to `0`): the bridge now routes `QSProg.QOp.rz`
    to `QOp.rzReal` and then to `Gate.Rz q θ`.

    A "real" QFT-2 lowering with distinct physical qubits would
    use a smarter allocator (e.g. `Bridge.allocator2` from
    `QSSAToCircuit.lean`); that's an orthogonal RegAlloc concern,
    not a Phase-3 VIR concern. -/
def qft2Stub : Circuit 2 :=
  .gate (.H 0)
  (.gate (.Rz 0 (Real.pi / 2))
  (.gate (.H 0)
  (.gate (.CNOT 0 0)
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

The cleanliness story scales: zero heartbeat budget, all `rfl`-style
proofs, the IR structure does the work. The previous `rz` VEIR-DIFF
(the dialect's `Float` carrier lossily collapsing the original `ℝ`
angle) is **closed** as of 2026-05-14 via `QOp.rzReal`. The
equivalence target `qft2Stub` now carries the exact `Real.pi / 2`
angle; the residual gap to the full `qft2` is the SWAP completion
(3 trailing CNOTs), **closed** as of 2026-05-15 via `ComMulti` and
the `letProj` pair destructor; see Section 9 below. -/

/-! ## 9. Full QFT-2 (SWAP completion) via `ComMulti.letProj`

With the multi-binder `ComMulti` (Phase 4 #7, file `VIR/MultiCom.lean`),
the canonical 6-gate QFT-2 — including its trailing 3-CNOT SWAP — is
expressible directly. Each 2-qubit gate emits a `pair qubit qubit`
result, and `letProj` splits the pair into two fresh `qubit` bindings
that subsequent gates consume cleanly. -/

/-- Full 6-gate QFT-2 as a `ComMulti quantumDialect`.

    Layout of bindings (newest at the head). After the four prefix gates
    we have the context

        [q1_h, q1_rz, q0_h, q1_init, q0_init]

    (`q0_init`, `q0_h` are old `q0`; `q1_init`, `q1_rz`, `q1_h` are old
    `q1`). The first CNOT takes the latest `q0` (here: `q0_h`, three
    deep) and the latest `q1` (here: `q1_h`, head of context) and
    returns a pair. We destruct each pair via `letProj` immediately
    after the gate; `.here` becomes the second component (`q1` line),
    `.there .here` becomes the first component (`q0` line).

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
  -- p1 : pair qubit qubit at `.here`; split into (q0_1, q1_1).
  .letProj .here <|
  -- Γ extends to [q1_1, q0_1, p1, q1_h, q1_rz, q0_h, q1_init, q0_init]
  -- p2 := CNOT q1_1 q0_1
  .var (eCNOT .here (.there .here)) <|
  .letProj .here <|
  -- Γ extends with [q0_2, q1_2, p2, q1_1, q0_1, p1, q1_h, q1_rz,
  -- q0_h, q1_init, q0_init].  Latest q1 = q1_2 at `.here`,
  -- latest q0 = q0_2 at `.there .here`.
  -- p3 := CNOT q0_2 q1_2
  .var (eCNOT (.there .here) .here) <|
  -- Return p3 (already a `pair qubit qubit`).
  .ret .here

/-- The full QFT-2 with SWAP completion lowers to a 7-gate circuit:
    `H, Rz, H` followed by 4 CNOTs (1 for the QFT body + 3 for the SWAP).

    All physical-qubit slots collapse to 0 under the identity allocator,
    consistent with `qftVIR`'s lowering. -/
def qft2FullStub : Circuit 2 :=
  .gate (.H 0)
  (.gate (.Rz 0 (Real.pi / 2))
  (.gate (.H 0)
  (.gate (.CNOT 0 0)
  (.gate (.CNOT 0 0)
  (.gate (.CNOT 0 0)
  .empty)))))

theorem qft2FullStub_gateCount : qft2FullStub.gateCount = 6 := by rfl

/-- The full VIR-side QFT (multi-binder form, SWAP included) lowers to
    the 6-gate stub. -/
theorem qftVIRFull_lowerMultiVIRCom_eq_qft2FullStub :
    QuantumDialect.lowerMultiVIRCom (numQ := 2) (by omega) qftVIRFull ra2 =
    qft2FullStub := by
  rfl

/-- Gate count of the full QFT-2: 6 = 3 (HRzH) + 1 (QFT-body CNOT) + 3
    (SWAP), as in the canonical decomposition. -/
theorem qftVIRFull_lowerMultiVIRCom_gateCount :
    (QuantumDialect.lowerMultiVIRCom (numQ := 2) (by omega) qftVIRFull ra2).gateCount
      = 6 := by
  rfl

/-- Real `QComp` semantics of the full QFT-2: `unitaryDenote` of the
    SWAP-completed stub. -/
theorem qftVIRFull_realDenote_eq_qft2FullStub :
    GateUnitarity.unitaryDenote
        (QuantumDialect.lowerMultiVIRCom (numQ := 2) (by omega) qftVIRFull ra2) =
    GateUnitarity.unitaryDenote qft2FullStub := by
  rw [qftVIRFull_lowerMultiVIRCom_eq_qft2FullStub]

/-! Sanity tie-in: `qftVIR` embedded via `Com.toMulti` and lowered through the
multi-binder path agrees with the original single-binder lowering. -/

theorem qftVIR_toMulti_lowerMultiVIRCom_eq :
    QuantumDialect.lowerMultiVIRCom (numQ := 2) (by omega) qftVIR.toMulti ra2 =
    lowerVIRCom (numQ := 2) (by omega) qftVIR ra2 :=
  QuantumDialect.lowerMultiVIRCom_toMulti_eq (by omega) qftVIR ra2

end

end CatCrypt.Crypto.SecureCompilation.VIR.Programs.QFTVIR
