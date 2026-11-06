"""Qrisp circuits through `catq-compile`.

`compile_qrisp(obj)` takes a Qrisp `QuantumSession` (or a `QuantumVariable`, whose session
is taken), compiles it with `QuantumSession.compile(**compile_kwargs)` (allocation, qubit
reuse, synthesis of multi-controlled gates; `compile_mcm=True` gives the mid-circuit
measurements of the `gidney` and `jones` methods), or takes a Qrisp `QuantumCircuit` as it
is, and then

1. decomposes, in Qrisp, every operation that Qrisp's converter does not send to a statement
   `catq-compile` reads (`QuantumCircuit.transpile` with a predicate; composite gates such as
   `QFT_dg` or the compiled Toffolis of the `jones` method),
2. converts to Qiskit (`QuantumCircuit.to_qiskit`) and replaces the remaining instructions
   outside the statements by their Qiskit definitions (`unroll`: `rzz`, `gphase`),
3. runs `VerifiedCompiler.compile`, which splits at barriers and classical instructions,
4. converts back with `qrisp.QuantumCircuit.from_qiskit`, which carries the global phase
   as a `gphase` gate.

The trusted base adds Qrisp's decomposition and conversion and the Qiskit definitions used
by `unroll` to that of `VerifiedCompiler` (`QRUNCH.md`, "What is trusted").
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Optional

from qiskit import QuantumCircuit

from .compiler import CompileReport, VerifiedCompiler
from .qasm_io import ANNOTATION, IDENTITY, STATEMENTS, is_classical

# Qrisp's names of the operations that `to_qiskit` sends to a statement of `STATEMENTS` or
# to a boundary; every other operation with a definition is decomposed in Qrisp.
QRISP_KEEP = set(STATEMENTS) | IDENTITY | ANNOTATION | {
    "s_dg", "t_dg", "sx_dg", "measure", "reset", "gphase", "rzz"}
UNROLL_REPS = 8


@dataclass
class QrispResult:
    """`circuit`: the Qrisp circuit of the output; `qiskit_in` and `qiskit_out`: the Qiskit
    circuits sent to and returned by the compiler; `report`: the compiler's report, with
    the phase (`report.phase`) and the bound (`report.eps`, `None` when unchecked)."""
    circuit: Any
    qiskit_in: QuantumCircuit
    qiskit_out: QuantumCircuit
    report: CompileReport

    @property
    def phase(self) -> float:
        return self.report.phase

    @property
    def eps(self) -> Optional[float]:
        return self.report.eps


def _known(ins) -> bool:
    name = ins.operation.name
    return name in STATEMENTS or name in IDENTITY or name in ANNOTATION or is_classical(ins)


def unroll(qc: QuantumCircuit, reps: int = UNROLL_REPS) -> QuantumCircuit:
    """`qc` with each instruction outside the statements and boundaries replaced by its
    Qiskit definition, repeatedly (at most `reps` times); what remains unknown is left for
    `VerifiedCompiler` to refuse."""
    for _ in range(reps):
        names = sorted({ins.operation.name for ins in qc.data if not _known(ins)})
        if not names:
            break
        qc = qc.decompose(gates_to_decompose=names)
    return qc


def qrisp_circuit(obj: Any, compile_kwargs: Optional[dict] = None):
    """The Qrisp `QuantumCircuit` of `obj`: `obj.compile(**compile_kwargs)` for a session (or
    the session of a quantum variable), `obj` itself for a circuit."""
    import qrisp

    # `QuantumSession` is a subclass of `QuantumCircuit`: test it first.
    qs = obj if isinstance(obj, qrisp.QuantumSession) else getattr(obj, "qs", None)
    if isinstance(qs, qrisp.QuantumSession):
        return qs.compile(**(compile_kwargs or {}))
    if isinstance(obj, qrisp.QuantumCircuit):
        return obj
    raise TypeError(f"expected a Qrisp QuantumSession, QuantumVariable or QuantumCircuit, "
                    f"got {type(obj).__name__}")


def to_qiskit(obj: Any, compile_kwargs: Optional[dict] = None) -> QuantumCircuit:
    """Steps 1 and 2: the Qiskit circuit, over the statements and boundaries, that
    `compile_qrisp` sends to the compiler."""
    qc = qrisp_circuit(obj, compile_kwargs)
    flat = qc.transpile(transpile_predicate=lambda op: op.name not in QRISP_KEEP)
    return unroll(flat.to_qiskit())


def compile_qrisp(obj: Any, compiler: Optional[VerifiedCompiler] = None,
                  compile_kwargs: Optional[dict] = None, **compiler_kwargs) -> QrispResult:
    """`obj` through `catq-compile`; `compiler` (else a `VerifiedCompiler(**compiler_kwargs)`,
    closed afterwards) does the work. A circuit the compiler refuses comes back unchanged,
    with the reason in `report.reason`."""
    import qrisp

    qin = to_qiskit(obj, compile_kwargs)
    own = compiler is None
    vc = VerifiedCompiler(**compiler_kwargs) if own else compiler
    try:
        qout = vc.compile(qin)
    finally:
        if own:
            vc.close()
    return QrispResult(qrisp.QuantumCircuit.from_qiskit(qout), qin, qout, vc.last_report)
