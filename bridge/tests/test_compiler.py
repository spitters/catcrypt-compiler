"""Tests of `catq.VerifiedCompiler` on the 12 Q-Synth VQE circuits and on one circuit
with every gate the lowering translates.

Each output is checked against its input: up to global phase (8 qubits: Qiskit
`Operator.equiv`; 16 qubits: four random statevectors, a common phase across them)
and exactly, with the global phase the compiler tracks.

usage (from bridge/): uv run python -P -m pytest tests -s
                  or: uv run python -P tests/test_compiler.py [FILE.qasm...]
"""
import cmath
import glob
import math
import os
import sys

for _v in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ.setdefault(_v, "1")

import numpy as np  # noqa: E402
import pytest
from qiskit import QuantumCircuit, qasm2, transpile
from qiskit.circuit import Parameter
from qiskit.circuit.library import CU1Gate, RYGate, U1Gate, U2Gate, U3Gate
from qiskit.quantum_info import Operator, Statevector, random_statevector

BRIDGE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, BRIDGE)
sys.path.insert(0, os.path.join(BRIDGE, "tests"))
from catq import VerifiedCompiler, decode_angle, encode_angle  # noqa: E402
from branching import same_distribution, segments_equiv  # noqa: E402

QSYNTH = sorted(glob.glob(os.path.join(os.path.dirname(BRIDGE), "bench", "qasm", "qsynth",
                                       "*.qasm")))
OUT_GATES = {"rx", "ry", "rz", "cx", "p", "barrier"}
TOL = 1e-8


def load(path: str) -> QuantumCircuit:
    return qasm2.load(path, custom_instructions=qasm2.LEGACY_CUSTOM_INSTRUCTIONS)


def simulate(qc: QuantumCircuit, states: np.ndarray) -> np.ndarray:
    """Each row of `states` (Qiskit's little-endian order) evolved by `qc`. Qiskit's
    `Statevector.evolve` takes about 4 ms per gate at 16 qubits; this takes 0.3 ms
    with single-threaded BLAS (multi-threaded BLAS is slower on these products)."""
    n = qc.num_qubits
    ops = []
    cache: dict = {}
    for ins in qc.data:
        op = ins.operation
        if op.name == "barrier":
            continue
        key = (op.name, tuple(float(p) for p in op.params))
        if key not in cache:
            cache[key] = Operator(op).data
        k = len(ins.qubits)
        # matrix axes: out q_{k-1}..q_0, in q_{k-1}..q_0; state axis of qubit q: n-1-q
        axes = [n - 1 - qc.find_bit(q).index for q in reversed(ins.qubits)]
        ops.append((cache[key].reshape((2,) * (2 * k)), k, axes))
    out = []
    for row in states:
        psi = row.reshape((2,) * n)
        for m, k, axes in ops:
            psi = np.moveaxis(np.tensordot(m, psi, axes=(list(range(k, 2 * k)), axes)),
                              list(range(k)), axes)
        out.append(psi.reshape(2 ** n))
    return cmath.exp(1j * float(qc.global_phase)) * np.array(out)


def check(qc_in: QuantumCircuit, qc_out: QuantumCircuit) -> dict:
    """`equiv`: equal up to global phase; `exact`: equal with the tracked phase."""
    assert set(qc_out.count_ops()) <= OUT_GATES, qc_out.count_ops()
    if qc_in.num_qubits <= 10:
        a, b = Operator(qc_in), Operator(qc_out)
        return {"equiv": a.equiv(b), "exact": bool(np.allclose(a.data, b.data, atol=TOL)),
                "method": "Operator"}
    states = np.array([random_statevector(2 ** qc_in.num_qubits, seed=s).data
                       for s in range(4)])
    a, b = simulate(qc_in, states), simulate(qc_out, states)
    ovs = [complex(np.vdot(x, y)) for x, y in zip(a, b)]
    ph = cmath.phase(ovs[0])
    equiv = all(abs(abs(o) - 1) < TOL and abs(cmath.phase(o / ovs[0])) < TOL for o in ovs)
    return {"equiv": equiv, "exact": equiv and abs(ph) < TOL, "method": "4 statevectors"}


# ------------------------------------------------------------- tests without Lean

@pytest.mark.parametrize("theta", [0.0, math.pi, -math.pi, 0.25, -1.3e-7, 2 * math.pi,
                                   math.pi / 4, 3.0])
def test_angle_round_trip(theta):
    q = decode_angle(encode_angle(theta))
    assert float(q) * math.pi == pytest.approx(theta, rel=1e-15, abs=1e-300)


def test_simulate_matches_statevector():
    qc = all_gates()
    qc.cx(2, 0); qc.rz(0.7, 1)
    states = np.array([random_statevector(8, seed=s).data for s in range(3)])
    ref = np.array([Statevector(s).evolve(qc).data for s in states])
    assert np.allclose(simulate(qc, states), ref)


# ------------------------------------------------------------- tests through catq-compile

def all_gates() -> QuantumCircuit:
    qc = QuantumCircuit(3, global_phase=0.3)
    a = [0.37, -1.1, 2.9]
    qc.h(0); qc.x(1); qc.y(2); qc.z(0); qc.s(1); qc.sdg(2); qc.t(0); qc.tdg(1)
    qc.sx(2); qc.sxdg(0); qc.id(1)
    qc.rx(a[0], 0); qc.ry(a[1], 1); qc.rz(a[2], 2); qc.p(a[0], 0)
    qc.append(U1Gate(a[1]), [1])
    qc.u(a[0], a[1], a[2], 2)
    qc.append(U3Gate(*a), [0])
    qc.append(U2Gate(a[0], a[2]), [1])
    qc.barrier()
    qc.cx(0, 1); qc.cz(1, 2); qc.swap(0, 2); qc.cp(a[2], 1, 0)
    qc.append(CU1Gate(a[0]), [2, 1])
    qc.ccx(0, 1, 2); qc.ccz(2, 0, 1)
    return qc


def run(qc: QuantumCircuit, name: str, level: int | str = 2, checked: bool = False) -> dict:
    vc = VerifiedCompiler(level=level, check=checked)
    out = vc.compile(qc)
    vc.close()
    rep = vc.last_report
    assert rep.optimized, rep.reason
    row = {"circuit": name, "qubits": qc.num_qubits, "cx_in": rep.cx_in,
           "cx_out": rep.cx_out, "gates_in": qc.size(), "gates_out": out.size(),
           "seconds": round(rep.seconds, 2),
           "eps": rep.rows[-1].split()[-1] if rep.rows else "0", **check(qc, out)}
    print("\t".join(str(v) for v in row.values()), flush=True)
    assert row["equiv"] and row["exact"], row
    return row


def test_all_gates():
    run(all_gates(), "all_gates")


def test_qrunch_gate_set():
    """An input over Qrunch's gate set {rx, ry, rz, cx, p}."""
    src = next(p for p in QSYNTH if p.endswith("simple_8q_50o_0.qasm"))
    qc = transpile(load(src), basis_gates=["rx", "ry", "rz", "cx", "p"],
                   optimization_level=0)
    run(qc, "simple_8q_50o_0 (qrunch basis)")


def test_level2r_qrunch_gate_set():
    """Level `2r` (Level 2 and KAK and ZYZ resynthesis, `ResynthLevel.resynth`) on the same
    input."""
    src = next(p for p in QSYNTH if p.endswith("simple_8q_50o_0.qasm"))
    qc = transpile(load(src), basis_gates=["rx", "ry", "rz", "cx", "p"],
                   optimization_level=0)
    row = run(qc, "simple_8q_50o_0 (qrunch basis, level 2r)", level="2r")
    assert row["cx_out"] <= run(qc, "simple_8q_50o_0 (qrunch basis)")["cx_out"]


@pytest.mark.parametrize("checked", [False, True], ids=["unchecked", "check"])
@pytest.mark.parametrize("src", QSYNTH, ids=lambda p: os.path.basename(p)[:-5])
def test_level2r_qsynth(src, checked):
    """Level `2r` on every Q-Synth circuit, with and without the checker: equal to the input
    with the tracked phase; with the checker a bound is reported, and both give the same
    circuit when every fit passes it."""
    name = os.path.basename(src)[:-5] + f" (level 2r, check={checked})"
    row = run(load(src), name, level="2r", checked=checked)
    assert (row["eps"] != "unchecked") == checked, row["eps"]


def test_unsupported_unchanged():
    qc = QuantumCircuit(2, 2)
    qc.h(0); qc.rx(Parameter("t"), 1); qc.measure(0, 0)
    vc = VerifiedCompiler()
    assert vc.compile(qc) is qc and not vc.last_report.optimized


def mid_circuit() -> QuantumCircuit:
    """Three qubits: a mid-circuit measurement, an `if_test` with an else branch, a reset
    and final measurements, with gates the compiler removes in each segment."""
    qc = QuantumCircuit(3, 3, global_phase=0.4)
    qc.h(0); qc.cx(0, 1); qc.rz(0.3, 1); qc.cx(0, 1); qc.t(2); qc.cx(1, 2); qc.cx(1, 2)
    qc.ry(0.9, 0)
    qc.measure(0, 0)
    qc.ry(0.7, 1); qc.h(0); qc.cx(1, 2); qc.s(2); qc.sdg(2); qc.h(1)
    with qc.if_test((qc.clbits[0], 1)) as orelse:
        qc.x(2); qc.rz(0.2, 1)
    with orelse:
        qc.h(2)
    qc.cx(1, 2); qc.cx(1, 2); qc.ry(1.1, 1); qc.rx(0.4, 2); qc.cx(2, 0); qc.cx(0, 1)
    qc.reset(0)
    qc.cx(2, 0); qc.ry(0.8, 0); qc.rz(0.5, 0); qc.rz(-0.1, 0)
    qc.measure([0, 1, 2], [0, 1, 2])
    return qc


@pytest.mark.parametrize("level", ["2", "2r"])
def test_mid_circuit_measurement(level):
    """Measurement, reset and `if_test` stay in place on their qubits and clbits; each
    unitary segment equals its input up to global phase (`Operator`), the measured
    distribution is the input's (exact branching simulation), and the input's global phase
    is kept."""
    qc = mid_circuit()
    vc = VerifiedCompiler(level=level, check=True)
    out = vc.compile(qc)
    vc.close()
    rep = vc.last_report
    assert rep.optimized and not rep.unitary, rep.reason
    assert rep.phase == 0.0 and float(out.global_phase) == pytest.approx(0.4)
    assert rep.eps is not None and len(rep.segment_phases) == 4
    assert segments_equiv(qc, out) == 7
    assert same_distribution(qc, out)
    assert rep.cx_out < rep.cx_in
    gates = {ins.operation.name for ins in out.data}
    assert gates <= OUT_GATES | {"measure", "reset", "if_else"}, gates


def test_branching_detects_change():
    """The distribution check separates circuits: an extra rotation on each qubit, before
    the mid-circuit measurement or after it, changes the distribution."""
    qc = mid_circuit()
    k = next(i for i, ins in enumerate(qc.data) if ins.operation.name == "measure")
    for at in (k, k + 1):
        for q in qc.qubits:
            bad = qc.copy()
            bad.data.insert(at, qc.data[0].replace(operation=RYGate(0.5), qubits=(q,)))
            assert not same_distribution(qc, bad), (at, q)


def test_final_measurements_only():
    """A unitary circuit followed by measurements is optimized; its phase is dropped."""
    qc = all_gates()
    qc.measure_all()
    vc = VerifiedCompiler()
    out = vc.compile(qc)
    vc.close()
    rep = vc.last_report
    assert rep.optimized and not rep.unitary
    assert float(out.global_phase) == pytest.approx(0.3)
    segments_equiv(qc, out)
    assert same_distribution(qc, out)


@pytest.mark.parametrize("path", QSYNTH, ids=[os.path.basename(p) for p in QSYNTH])
def test_qsynth(path):
    run(load(path), os.path.basename(path).removesuffix(".qasm"))


if __name__ == "__main__":
    print("circuit\tqubits\tcx_in\tcx_out\tgates_in\tgates_out\tseconds\tequiv\texact\tmethod")
    for p in sys.argv[1:] or QSYNTH:
        run(load(p), os.path.basename(p).removesuffix(".qasm"))
