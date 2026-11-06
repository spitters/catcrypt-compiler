"""Checks of a compiled circuit with classical instructions against its input.

`distribution` computes the exact distribution of the final classical register of a
circuit with mid-circuit measurements, resets and `if_test`, by following every branch of
the state vector; `segments_equiv` compares the unitary segments between classical
boundaries by Qiskit's `Operator`, up to global phase.
"""
from __future__ import annotations

import os
import sys
from collections import defaultdict

import numpy as np
from qiskit import QuantumCircuit
from qiskit.circuit import Clbit, ClassicalRegister, IfElseOp
from qiskit.circuit.library import get_standard_gate_name_mapping
from qiskit.quantum_info import Operator, Statevector

BRIDGE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, BRIDGE)
from catq.qasm_io import split_segments  # noqa: E402

PROJ = (np.diag([1.0, 0.0]), np.diag([0.0, 1.0]))
X = np.array([[0.0, 1.0], [1.0, 0.0]])
CUTOFF = 1e-14
GATES = get_standard_gate_name_mapping()


def _condition(cond, bits: dict) -> bool:
    target, value = cond
    if isinstance(target, Clbit):
        return bits[target] == int(value)
    if isinstance(target, ClassicalRegister):
        return sum(bits[b] << i for i, b in enumerate(target)) == int(value)
    raise NotImplementedError(f"condition {cond!r}")


def _run(qc: QuantumCircuit, qmap: dict, cmap: dict, branches: list) -> list:
    """`branches`: (probability, state, {outer clbit: bit}); `qmap`/`cmap` send the bits of
    `qc` to the outer qubit indices and clbits."""
    for ins in qc.data:
        op = ins.operation
        qs = [qmap[q] for q in ins.qubits]
        cs = [cmap[c] for c in ins.clbits]
        nxt = []
        for p, psi, bits in branches:
            if op.name == "barrier":
                nxt.append((p, psi, bits))
            elif op.name in ("measure", "reset"):
                for b in (0, 1):
                    phi = psi.evolve(Operator(PROJ[b]), [qs[0]])
                    pb = float(np.vdot(phi.data, phi.data).real)
                    if pb < CUTOFF:
                        continue
                    phi = Statevector(phi.data / np.sqrt(pb))
                    nb = dict(bits)
                    if op.name == "measure":
                        nb[cs[0]] = b
                    elif b == 1:
                        phi = phi.evolve(Operator(X), [qs[0]])
                    nxt.append((p * pb, phi, nb))
            elif isinstance(op, IfElseOp):
                taken = _condition(op.condition, bits)
                body = op.blocks[0] if taken else (op.blocks[1] if len(op.blocks) > 1 else None)
                if body is None:
                    nxt.append((p, psi, bits))
                    continue
                inner_q = {bq: ins.qubits[i] for i, bq in enumerate(body.qubits)}
                inner_c = {bc: ins.clbits[i] for i, bc in enumerate(body.clbits)}
                nxt.extend(_run(body, {k: qmap[v] for k, v in inner_q.items()},
                                {k: cmap[v] for k, v in inner_c.items()}, [(p, psi, bits)]))
            else:
                nxt.append((p, psi.evolve(Operator(op), qs), bits))
        branches = nxt
    return branches


def distribution(qc: QuantumCircuit) -> dict[str, float]:
    """The probability of each final value of the clbits (Qiskit's order: clbit 0 last),
    from the all-zero state."""
    psi = Statevector.from_int(0, 2 ** qc.num_qubits)
    qmap = {q: i for i, q in enumerate(qc.qubits)}
    cmap = {c: c for c in qc.clbits}
    out: dict[str, float] = defaultdict(float)
    for p, _, bits in _run(qc, qmap, cmap, [(1.0, psi, {c: 0 for c in qc.clbits})]):
        out["".join(str(bits[c]) for c in reversed(qc.clbits))] += p
    return dict(out)


def same_distribution(a: QuantumCircuit, b: QuantumCircuit, tol: float = 1e-9) -> bool:
    da, db = distribution(a), distribution(b)
    return all(abs(da.get(k, 0.0) - db.get(k, 0.0)) < tol for k in set(da) | set(db))


def _segment_circuit(n: int, seg) -> QuantumCircuit:
    qc = QuantumCircuit(n)
    for name, angs, qs in seg.ops:
        qc.append(GATES[name].base_class(*angs), qs)
    return qc


def segments_equiv(a: QuantumCircuit, b: QuantumCircuit) -> int:
    """Asserts that `a` and `b` have the same boundary instructions, on the same qubits and
    clbits, and unitary segments equal up to global phase (`Operator.equiv`); returns the
    number of segments."""
    sa, na, _ = split_segments(a)
    sb, nb, _ = split_segments(b)
    assert len(sa) == len(sb)
    for x, y in zip(na, nb):
        assert x.operation.name == y.operation.name
        assert [a.find_bit(q).index for q in x.qubits] == [b.find_bit(q).index for q in y.qubits]
        assert [a.find_bit(c).index for c in x.clbits] == [b.find_bit(c).index for c in y.clbits]
    for i, (x, y) in enumerate(zip(sa, sb)):
        ox = Operator(_segment_circuit(a.num_qubits, x))
        oy = Operator(_segment_circuit(b.num_qubits, y))
        assert ox.equiv(oy), f"segment {i}"
    return len(sa)
