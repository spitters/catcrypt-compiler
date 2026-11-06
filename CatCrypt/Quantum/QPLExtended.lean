/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.QPL
public import CatCrypt.Quantum.Instrument

/-!
# Extended QPL: Custom Operation Sets and Example Programs

Standard QPL (`QPL n α`, which is `XQPL Empty n α`) can only apply gates from the
fixed `Gate n` type. Programs like Grover (oracle queries), BB84 (custom state
preparation), Deutsch-Jozsa (function oracle), etc. require operations beyond the
Clifford+T gate set; they are `XQPL Ops n α` programs, whose `custom` constructor
injects an operation from `Ops`, given semantics by an `OpDenote Ops n` instance.
`XQPL`, `OpDenote` and the semantics live in `CatCrypt.Quantum.QPL`.

## Main definitions

* `ProgramLevel` — classification of quantum program expressiveness
* Example operation sets: `GroverOps`, `BB84Ops`, `OracleOps`

## References

* Selinger, P. — *Towards a Quantum Programming Language*, MSCS 2004
* Green et al. — *Quipper: A Scalable Quantum Programming Language*, PLDI 2013
-/

@[expose] public section

set_option autoImplicit true

open CatCrypt.Quantum CatCrypt.Quantum.QPL CatCrypt.Quantum.QCircuit

noncomputable section

namespace CatCrypt.Quantum.QPLExtended

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
