"""Tests of `catq.qrisp_adapter` on Qrisp programs: QPE, QAOA MaxCut at fixed angles, and a
program with the mid-circuit measurements of the `gidney` and `jones` methods. Skipped when
qrisp is not installed (`uv sync --extra qrisp`).

Each output is checked against the Qiskit circuit the adapter sends to the compiler: exactly
with the reported phase (`Operator`) for a unitary program; per unitary segment up to phase
and by the exact distribution of the clbits for a program with measurements. The Qrisp circuit
returned is checked against the Qiskit output.
"""
import os
import sys

import networkx as nx
import numpy as np
import pytest
from qiskit.quantum_info import Operator

qrisp = pytest.importorskip("qrisp")

BRIDGE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, BRIDGE)
sys.path.insert(0, os.path.join(BRIDGE, "tests"))
from catq.qrisp_adapter import compile_qrisp, to_qiskit  # noqa: E402
from branching import same_distribution, segments_equiv  # noqa: E402

OUT_GATES = {"rx", "ry", "rz", "cx", "p"}
TOL = 1e-8


def qpe_session():
    from qrisp import QPE, QuantumVariable, h, p

    def u(qv):
        p(2 * np.pi / 8, qv[0])
        p(2 * np.pi / 4, qv[1])

    qv = QuantumVariable(2)
    h(qv)
    return QPE(qv, u, precision=3).qs


def qaoa_circuit():
    from qrisp import QuantumVariable
    from qrisp.qaoa import maxcut_problem

    g = nx.Graph([(0, 1), (1, 2), (2, 3), (3, 0), (0, 2)])
    qc, syms = maxcut_problem(g).compile_circuit(QuantumVariable(len(g)), 2)
    return qc.bind_parameters({s: 0.3 + 0.1 * i for i, s in enumerate(syms)})


def mcm_circuit():
    """Two logical ANDs (`gidney`, `jones`), each uncomputed, compiled with
    `compile_mcm=True` and measured."""
    from qrisp import QuantumBool, QuantumVariable, cx, h, mcx, ry

    a = QuantumVariable(4)
    h(a)
    ry(0.3, a[1])
    b = QuantumBool()
    mcx(a[:2], b, method="gidney")
    cx(b, a[3])
    b.uncompute()
    c = QuantumBool()
    mcx(a[1:3], c, method="jones")
    cx(c, a[0])
    ry(0.8, a[2])
    c.uncompute()
    qc = a.qs.compile(compile_mcm=True)
    for qb in a:
        qc.measure(qb)
    return qc


def check_unitary(res):
    rep = res.report
    assert rep.optimized and rep.unitary, rep.reason
    assert {i.operation.name for i in res.qiskit_out.data} <= OUT_GATES | {"barrier"}
    a, b = Operator(res.qiskit_in), Operator(res.qiskit_out)
    assert np.allclose(a.data, b.data, atol=TOL)
    assert Operator(res.circuit.to_qiskit()).equiv(b)
    # the CNOT count of the imported gates (cp, cz, ccx lowered) is field 2 of each row
    assert rep.cx_out <= sum(int(r.split()[2]) for r in rep.rows)


def test_qpe():
    res = compile_qrisp(qpe_session(), check=True)
    # a session is compiled (qubit reuse) before conversion
    assert res.qiskit_in.num_qubits == qpe_session().compile().num_qubits()
    check_unitary(res)
    assert res.eps is not None


def test_qaoa():
    res = compile_qrisp(qaoa_circuit(), level="2r")
    check_unitary(res)
    assert res.eps is None


def test_mid_circuit_measurements():
    qin = to_qiskit(mcm_circuit())
    names = {i.operation.name for i in qin.data}
    assert {"measure", "reset", "if_else"} <= names, names
    res = compile_qrisp(mcm_circuit(), check=True)
    rep = res.report
    assert rep.optimized and not rep.unitary, rep.reason
    assert rep.phase == 0.0
    segments_equiv(res.qiskit_in, res.qiskit_out)
    assert same_distribution(res.qiskit_in, res.qiskit_out)
    back = res.circuit.to_qiskit()
    assert back.count_ops().get("measure", 0) == res.qiskit_out.count_ops()["measure"]
