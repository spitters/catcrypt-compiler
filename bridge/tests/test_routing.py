"""Tests of `catq.compile_for_device` on two 6-qubit circuits (one whose first compile leaves
a CX graph that fits both maps, one that needs routing swaps), each routed onto a line and
onto a 2x3 grid: the output equals the input through its layout (`Operator.from_circuit`,
global phase included), no two-qubit gate is off the map, and the output has at most the CX
of the routed circuit before the second compile and of the input routed without catq-compile.

usage (from bridge/): uv run pytest -q tests/test_routing.py
"""
import math
import os
import sys

for _v in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ.setdefault(_v, "1")

import numpy as np  # noqa: E402
import pytest  # noqa: E402
from qiskit import QuantumCircuit  # noqa: E402
from qiskit.quantum_info import Operator  # noqa: E402
from qiskit.transpiler import CouplingMap  # noqa: E402

BRIDGE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, BRIDGE)
from catq import VerifiedCompiler, compile_for_device, cx_count  # noqa: E402
from catq.routing import OffMapGate, bare, off_map_gates, route, symmetric_map  # noqa: E402

SEEDS = 20
OUT_GATES = {"rx", "ry", "rz", "cx", "p"}
MAPS = {"line": CouplingMap.from_line(6, bidirectional=False),
        "grid": CouplingMap.from_grid(2, 3, bidirectional=False)}


def six_qubits() -> QuantumCircuit:
    """Long-range CX, swaps (elided by the first compile), a cancelling CX pair and rotations
    that merge."""
    qc = QuantumCircuit(6)
    for q in range(6):
        qc.h(q)
    qc.cx(0, 5)
    qc.rz(math.pi / 8, 5)
    qc.cx(0, 5)
    qc.swap(1, 4)
    qc.cx(1, 3)
    qc.cx(1, 3)
    qc.rx(0.3, 3)
    qc.cx(2, 4)
    qc.rz(0.2, 4)
    qc.rz(0.5, 4)
    qc.cx(2, 4)
    qc.swap(0, 2)
    qc.cx(0, 4)
    qc.ry(math.pi / 4, 0)
    qc.cx(5, 1)
    qc.t(1)
    qc.cx(3, 0)
    qc.s(2)
    qc.cx(2, 5)
    return qc


def dense() -> QuantumCircuit:
    """CX on every pair of six qubits between rotations, and two swaps: after the first compile
    the CX graph is not a subgraph of either map, so routing inserts swaps."""
    qc = QuantumCircuit(6)
    k = 0
    for a in range(6):
        for b in range(a + 1, 6):
            qc.cx(a, b)
            qc.rz(0.1 * (k + 1), b)
            qc.ry(math.pi / 8, a)
            k += 1
    qc.swap(0, 3)
    qc.swap(2, 5)
    for a in range(6):
        qc.cx(a, (a + 3) % 6)
        qc.rx(0.25, a)
    return qc


CIRCUITS = {"six": six_qubits, "dense": dense}


@pytest.fixture(scope="module")
def vc():
    c = VerifiedCompiler(level="2r", check=True, permutation="layout")
    yield c
    c.close()


@pytest.mark.parametrize("circ", sorted(CIRCUITS))
@pytest.mark.parametrize("name", sorted(MAPS))
def test_compile_for_device(vc, circ, name):
    qc = CIRCUITS[circ]()
    cmap = MAPS[name]
    res = compile_for_device(qc, cmap, seeds=SEEDS, compiler=vc)
    assert res.pre.optimized and res.post.optimized, (res.pre.reason, res.post.reason)
    assert res.pre.final_permutation != list(range(6))  # the swaps were elided
    assert res.eps is not None and res.eps < 1e-6
    out = res.circuit
    assert out.layout is res.layout
    assert set(out.count_ops()) <= OUT_GATES
    assert off_map_gates(out, symmetric_map(cmap)) == []
    # Equal to the input through the layout, the global phase included.
    assert np.allclose(Operator.from_circuit(out).data, Operator(qc).data, atol=1e-6)
    # CX: at most the routed circuit before the second compile, and at most the input routed
    # by the same router with no catq-compile.
    assert res.cx_out <= res.cx_routed
    nothing, _ = route(bare(qc), symmetric_map(cmap), SEEDS)
    assert res.cx_out <= cx_count(nothing)
    if circ == "dense":
        assert res.cx_routed > res.cx_pre  # routing inserted swaps
        assert res.layout.final_layout is not None
    print(f"{circ} on {name}: cx in {cx_count(qc)}, route-then-nothing {cx_count(nothing)}, "
          f"pre {res.cx_pre}, routed {res.cx_routed}, out {res.cx_out}, eps {res.eps:.1e}")


def test_off_map_gates():
    qc = six_qubits()
    cmap = symmetric_map(MAPS["line"])
    assert off_map_gates(qc, cmap)  # cx(0, 5) is not an edge of the line
    routed, _ = route(qc, cmap, 2)
    assert off_map_gates(routed, cmap) == []


def test_rejects_layout_and_size(vc):
    qc = six_qubits()
    routed, _ = route(qc, symmetric_map(MAPS["line"]), 1)
    with pytest.raises(ValueError):
        compile_for_device(routed, MAPS["line"], compiler=vc)
    with pytest.raises(ValueError):
        compile_for_device(qc, CouplingMap.from_line(4), compiler=vc)
    assert issubclass(OffMapGate, RuntimeError)
