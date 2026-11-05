/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.QPL
public import CatCrypt.Quantum.Instrument

/-!
# Extended QPL: Parametric over Custom Operations

Standard QPL (`QPL n α`) can only apply gates from the fixed `Gate n` type.
Programs like Grover (oracle queries), BB84 (custom state preparation),
Deutsch-Jozsa (function oracle), etc. cannot be directly expressed because
they require operations beyond the Clifford+T gate set.

`XQPL Ops n α` extends QPL with a `custom` constructor that injects an
arbitrary operation from a user-supplied type `Ops`. The semantics of
custom operations are provided by an `OpDenote` typeclass instance.

## Main definitions

* `OpDenote Ops n` — typeclass giving denotational semantics to custom ops
* `XQPL Ops n α` — extended QPL with custom operations
* `XQPL.denote` — denotational semantics into `QComp (2^n) α`
* `QPL.toXQPL` — embedding of standard QPL into `XQPL Empty n α`; it preserves
  the denotation (`QPL.toXQPL_preserves_denote`)
* `ProgramLevel` — classification of quantum program expressiveness
* Example operation sets: `GroverOps`, `BB84Ops`, `OracleOps`

## References

* Selinger, P. — *Towards a Quantum Programming Language*, MSCS 2004
* Green et al. — *Quipper: A Scalable Quantum Programming Language*, PLDI 2013
-/

@[expose] public section

set_option autoImplicit true

open CatCrypt.Quantum CatCrypt.Quantum.QPL.QPL CatCrypt.Quantum.QCircuit

noncomputable section

namespace CatCrypt.Quantum.QPLExtended

/-! ## OpDenote Typeclass -/

/-- Typeclass providing denotational semantics for a custom operation set.
    Each operation in `Ops` is interpreted as a `QComp` on `2^n` dimensions. -/
class OpDenote (Ops : Type) (n : ℕ) where
  denote : Ops → QComp (2 ^ n) Unit

/-! ## Extended QPL Syntax -/

/-- Extended QPL: a quantum programming language parametric over custom operations.

    * `ret a` — return classical value `a`
    * `gate g k` — apply standard gate `g`, continue with `k`
    * `meas i kt kf` — measure qubit `i`, branch on outcome
    * `custom op k` — apply custom operation `op`, continue with `k`
    * `fail` — abort (probability 0 branch) -/
inductive XQPL (Ops : Type) (n : ℕ) : Type → Type 1 where
  | ret {α : Type} : α → XQPL Ops n α
  | gate {α : Type} : Gate n → XQPL Ops n α → XQPL Ops n α
  | meas {α : Type} : Fin n → XQPL Ops n α → XQPL Ops n α → XQPL Ops n α
  | custom {α : Type} : Ops → XQPL Ops n α → XQPL Ops n α
  | fail {α : Type} : XQPL Ops n α

namespace XQPL

variable {Ops : Type} {n : ℕ} {α β : Type}

/-! ## Denotational Semantics -/

/-- Denotational semantics for XQPL: interpret as a `QComp`. -/
def denote [OpDenote Ops n] : XQPL Ops n α → QComp (2 ^ n) α
  | .ret a => QComp.qpure a
  | .gate g k => QComp.qbind (GateUnitarity.denoteGateU g) (fun () => k.denote)
  | .meas i kt kf =>
    QComp.qbind (QPL.QPL.measQubit i) fun b =>
      if b then kt.denote else kf.denote
  | .custom op k => QComp.qbind (OpDenote.denote op) (fun () => k.denote)
  | .fail => QComp.qfail

/-! ## Gate Count -/

/-- Gate count: number of gate + measurement + custom operations on longest path. -/
def gateCount : XQPL Ops n α → ℕ
  | .ret _ => 0
  | .gate _ k => 1 + k.gateCount
  | .meas _ kt kf => 1 + max kt.gateCount kf.gateCount
  | .custom _ k => 1 + k.gateCount
  | .fail => 0

/-! ## Monadic Bind -/

/-- Monadic bind: substitute at `ret` leaves. -/
def bind : XQPL Ops n α → (α → XQPL Ops n β) → XQPL Ops n β
  | .ret a, f => f a
  | .gate g k, f => .gate g (k.bind f)
  | .meas i kt kf, f => .meas i (kt.bind f) (kf.bind f)
  | .custom op k, f => .custom op (k.bind f)
  | .fail, _ => .fail

/-! ## Structural Properties -/

@[simp] theorem denote_ret [OpDenote Ops n] (a : α) :
    (XQPL.ret a : XQPL Ops n α).denote = QComp.qpure a := rfl

@[simp] theorem denote_fail [OpDenote Ops n] :
    (XQPL.fail : XQPL Ops n α).denote = QComp.qfail := rfl

@[simp] theorem gateCount_ret (a : α) :
    (XQPL.ret a : XQPL Ops n α).gateCount = 0 := rfl

@[simp] theorem gateCount_fail :
    (XQPL.fail : XQPL Ops n α).gateCount = 0 := rfl

@[simp] theorem bind_ret (a : α) (f : α → XQPL Ops n β) :
    (XQPL.ret a).bind f = f a := rfl

@[simp] theorem bind_fail (f : α → XQPL Ops n β) :
    (XQPL.fail : XQPL Ops n α).bind f = .fail := rfl

end XQPL

/-! ## Embedding QPL into XQPL -/

/-- Embed standard QPL into XQPL with `Empty` operation set (no custom ops). -/
def QPL.toXQPL : CatCrypt.Quantum.QPL.QPL n α → XQPL Empty n α
  | .ret a => .ret a
  | .gate g k => .gate g (QPL.toXQPL k)
  | .meas i kt kf => .meas i (QPL.toXQPL kt) (QPL.toXQPL kf)
  | .fail => .fail

/-- Empty has no inhabitants, so OpDenote is trivially provided. -/
instance : OpDenote Empty n where
  denote e := e.elim

/-- The embedding of QPL into XQPL preserves the denotation. -/
theorem QPL.toXQPL_preserves_denote (p : CatCrypt.Quantum.QPL.QPL n α) :
    (QPL.toXQPL p).denote = p.denote := by
  induction p with
  | ret a => rfl
  | gate g k ih =>
    simp only [QPL.toXQPL, XQPL.denote, CatCrypt.Quantum.QPL.QPL.denote]
    congr 1; funext; exact ih
  | meas i kt kf iht ihf =>
    simp only [QPL.toXQPL, XQPL.denote, CatCrypt.Quantum.QPL.QPL.denote]
    congr 1; funext b; split <;> assumption
  | fail => rfl

/-! ## Example Operation Sets -/

/-- Grover oracle: marks a target basis state with a phase flip. -/
structure GroverOps where
  target : Fin 4

/-- Placeholder denotation for Grover oracle (full oracle requires 4×4 diagonal). -/
instance : OpDenote GroverOps 2 where
  denote _ := QComp.qpure ()

/-- BB84 operations: prepare a qubit in a given basis and bit value. -/
inductive BB84Ops where
  | prepare (basis bit : Fin 2)

/-- Placeholder denotation for BB84 preparation. -/
instance : OpDenote BB84Ops 1 where
  denote _ := QComp.qpure ()

/-- General oracle call (for Deutsch-Jozsa, Bernstein-Vazirani, Simon, etc.). -/
structure OracleOps (n : ℕ) where
  oracle : Unit

/-- Placeholder denotation for a general oracle. -/
instance : OpDenote (OracleOps n) n where
  denote _ := QComp.qpure ()

/-! ## Example Programs -/

/-- Grover's algorithm (1 iteration) on 2 qubits with oracle marking state `w`.
    H⊗H → Oracle → H⊗H → X⊗X → CZ → X⊗X → H⊗H -/
def groverXQPL (w : Fin 4) : XQPL GroverOps 2 Unit :=
  .gate (.H 0) (.gate (.H 1) (.custom ⟨w⟩
    (.gate (.H 0) (.gate (.H 1)
      (.gate (.X 0) (.gate (.X 1)
        (.gate (.CZ 0 1)
          (.gate (.X 0) (.gate (.X 1)
            (.gate (.H 0) (.gate (.H 1) (.ret ()))))))))))))

/-- BB84 prepare-and-measure: prepare qubit, then measure. -/
def bb84XQPL (basis bit : Fin 2) : XQPL BB84Ops 1 Bool :=
  .custom (.prepare basis bit) (.meas 0 (.ret true) (.ret false))

/-- Deutsch-Jozsa algorithm on 2 qubits: H⊗H → Oracle → H⊗H → Measure. -/
def deutschJozsaXQPL : XQPL (OracleOps 2) 2 Bool :=
  .gate (.H 0) (.gate (.H 1) (.custom ⟨()⟩
    (.gate (.H 0) (.gate (.H 1)
      (.meas 0 (.ret true) (.ret false))))))

/-! ## Program Level Classification -/

/-- Classification of quantum program expressiveness levels.

    * `pureMeasFree` — purely unitary, no measurements (e.g., Bell pair, QFT)
    * `pureWithMeas` — uses measurements but no custom ops (e.g., teleportation)
    * `needsOracle` — requires an oracle operation (e.g., Grover, Deutsch-Jozsa)
    * `needsCustomOp` — requires a custom non-oracle operation (e.g., BB84 prepare)
    * `registerLevel` — uses register-level operations (QFT, QPE, Trotter, etc.) -/
inductive ProgramLevel where
  | pureMeasFree
  | pureWithMeas
  | needsOracle
  | needsCustomOp
  | registerLevel
  deriving Repr, BEq

end CatCrypt.Quantum.QPLExtended
