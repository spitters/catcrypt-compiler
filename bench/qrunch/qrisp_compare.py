"""Circuits of Qrisp's algorithm library through catq-compile (the verified Lean compiler of the
Qrunch bridge, via `catq.qrisp_adapter`) against Qiskit transpile(optimization_level=3), both
into the basis {rx, ry, rz, cx, p}.

Each program is built with Qrisp at fixed parameters, compiled by `QuantumSession.compile`
and converted to Qiskit over the statements catq-compile reads (`qrisp_adapter.to_qiskit`);
that one Qiskit circuit is the input of both compilers. Per circuit, interleaved, best of
REPEAT, in one process:
  ours_ms    `VerifiedCompiler.compile` (segmentation, printing, one `catq-compile --serve`
             request per segment, reading back), level 2r, one server for the whole run
  qiskit_ms  transpile(optimization_level=3, basis above, seed 0)
and for both outputs: CX count, two-qubit depth, gate count (measurements, resets and barriers
not counted; an `if_else` counts as one), and the deviation from the input: for a unitary
circuit max |A - B| entrywise (Operator up to 10 qubits, else four random statevectors), ours
with its phase, Qiskit's through the output permutation its layout records; for a circuit with
classical instructions (`*_mcm` rows), the largest deviation of a unitary segment from its
input up to a phase, over four random statevectors, for ours only (Qiskit moves gates across
measurements, so its segments do not align: `-`). `cx_in` is the CX count of the input as
catq-compile imports it (cp, cz, swap and ccx lowered). Qiskit's level 3 elides SWAP gates into
an output permutation (`ElidePermutations`; `qiskit_perm` = yes when it did), which ours does
not; `qiskit_ne_cx` and `qiskit_ne_gates` are its counts with that pass removed.

usage: cd bridge && uv sync --extra qrisp && uv run python -I ../bench/qrunch/qrisp_compare.py
       [--check] [--out NAME.tsv] [CIRCUIT ...]; writes bench/qrunch/qrisp/results.tsv or NAME.tsv
"""
from __future__ import annotations

import cmath
import os
import sys
import time

import networkx as nx
import numpy as np
from qiskit import QuantumCircuit, transpile
from qiskit.quantum_info import Operator, Statevector, random_statevector

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "bridge"))
from catq import VerifiedCompiler  # noqa: E402
from catq.qasm_io import split_segments  # noqa: E402
from catq.qrisp_adapter import to_qiskit  # noqa: E402

BASIS = ["rx", "ry", "rz", "cx", "p"]
REPEAT = 5
NOT_GATES = {"measure", "reset", "barrier"}
OUT_DIR = os.path.join(HERE, "qrisp")


# --------------------------------------------------------------------------- programs

def qpe():
    """QPE at precision 4 of a two-qubit unitary with eigenphases off the grid."""
    from qrisp import QPE, QuantumVariable, cx, h, p, ry

    def u(qv):
        p(0.7, qv[0])
        cx(qv[0], qv[1])
        p(1.3, qv[1])
        cx(qv[0], qv[1])

    qv = QuantumVariable(2)
    h(qv[0])
    ry(0.4, qv[1])
    return QPE(qv, u, precision=4).qs, {}


def _order_finding(a: int, n: int, adder=None):
    """The circuit of Qrisp's `shor._find_order(a, n)` before its measurement."""
    from qrisp import QFT, QuantumFloat, QuantumModulus, control, h

    qg = QuantumModulus(n, adder)
    qg[:] = 1
    res = QuantumFloat(2 * qg.size + 1, exponent=-(2 * qg.size + 1))
    h(res)
    for qb in res:
        with control(qb):
            qg *= a
            a = (a * a) % n
    QFT(res, inv=True, inpl_adder=adder)
    return res.qs


def shor15():
    """Order finding of 7 modulo 15 (Qrisp's default Fourier adder)."""
    return _order_finding(7, 15), {}


def shor15_mcm():
    """Order finding of 7 modulo 15 with Gidney's adder, compiled with mid-circuit
    measurements (`compile_mcm=True`)."""
    from qrisp import gidney_adder
    return _order_finding(7, 15, gidney_adder), {"compile_mcm": True}


def _bind(qc, syms):
    return qc.bind_parameters({s: 0.3 + 0.17 * i for i, s in enumerate(syms)})


def qaoa_maxcut():
    """QAOA MaxCut, depth 3, on a 6-vertex graph (ring with two chords), fixed angles."""
    from qrisp import QuantumVariable
    from qrisp.qaoa import maxcut_problem

    g = nx.Graph([(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0), (0, 3), (1, 4)])
    qc, syms = maxcut_problem(g).compile_circuit(QuantumVariable(len(g)), 3)
    return _bind(qc, syms), {}


def vqe_heisenberg():
    """VQE for the Heisenberg model on a 6-site ring (J=1, B=0.5), Qrisp's ansatz, depth 2,
    fixed parameters."""
    from qrisp import QuantumVariable
    from qrisp.vqe.problems.heisenberg import heisenberg_problem

    g = nx.cycle_graph(6)
    qc, syms = heisenberg_problem(g, 1, 0.5).compile_circuit(QuantumVariable(6), 2)
    return _bind(qc, syms), {}


def grover():
    """Grover search for one marked value of a 5-qubit variable (`tag_state` oracle)."""
    from qrisp import QuantumFloat
    from qrisp.grover import grovers_alg, tag_state

    qf = QuantumFloat(5)
    grovers_alg(qf, lambda q: tag_state({q: 11}), winner_state_amount=1)
    return qf.qs, {}


def qft8():
    """Qrisp's QFT on 8 qubits applied to a basis state."""
    from qrisp import QFT, QuantumFloat

    qf = QuantumFloat(8)
    qf[:] = 77
    QFT(qf)
    return qf.qs, {}


def dicke():
    """Dicke state |D^6_3> (Qrisp's deterministic preparation)."""
    from qrisp import QuantumVariable, dicke_state, x

    qv = QuantumVariable(6)
    x(qv[3:])
    dicke_state(qv, 3)
    return qv.qs, {}


PROGRAMS = {f.__name__: f for f in (qpe, shor15, shor15_mcm, qaoa_maxcut, vqe_heisenberg,
                                    grover, qft8, dicke)}


# --------------------------------------------------------------------------- figures

def figures(qc: QuantumCircuit) -> tuple[int, int, int]:
    ops = qc.count_ops()
    depth2 = qc.depth(lambda ins: ins.operation.num_qubits == 2)
    gates = sum(v for k, v in ops.items() if k not in NOT_GATES)
    return int(ops.get("cx", 0)), depth2, gates


def _states(n: int):
    return [Statevector(random_statevector(2 ** n, seed=s)) for s in range(4)]


def _unpermute(data: np.ndarray, b: QuantumCircuit) -> np.ndarray:
    """A state on the physical qubits of `b` read on its virtual qubits: Qiskit's level 3
    elides final swaps into an output permutation (`ElidePermutations`, recorded in
    `b.layout`)."""
    if b.layout is None:
        return data
    p = b.layout.final_index_layout(filter_ancillas=True)
    n = len(p)
    t = data.reshape((2,) * n)
    return t.transpose([n - 1 - p[n - 1 - k] for k in range(n)]).reshape(2 ** n)


def deviation(a: QuantumCircuit, b: QuantumCircuit) -> float:
    """max |A - B| entrywise (Operator, through the output permutation of `b.layout`) or
    over four statevectors; NaN above 20 qubits."""
    if a.num_qubits > 20:
        return float("nan")
    if a.num_qubits <= 10:
        return float(np.abs(Operator(a).data - Operator.from_circuit(b).data).max())
    return max(float(np.abs(v.evolve(a).data - _unpermute(v.evolve(b).data, b)).max())
               for v in _states(a.num_qubits))


def no_elide_pass_manager():
    """Qiskit's level-3 preset pass manager into BASIS without `ElidePermutations`, whose
    output is the input's unitary on the same qubits, as ours is."""
    from qiskit.transpiler import PassManager, generate_preset_pass_manager
    from qiskit.transpiler.passes import ElidePermutations

    pm = generate_preset_pass_manager(3, basis_gates=BASIS, seed_transpiler=0)
    init = PassManager()
    for group in pm.init._tasks:
        tasks = [t for t in group if not isinstance(t, ElidePermutations)]
        if tasks:
            init.append(tasks)
    pm.init = init
    return pm


def permuted(b: QuantumCircuit) -> str:
    """`yes` when `b`'s layout records a non-trivial output permutation."""
    if b.layout is None:
        return "no"
    p = b.layout.final_index_layout(filter_ancillas=True)
    return "no" if list(p) == list(range(len(p))) else "yes"


def _segment(n: int, seg) -> QuantumCircuit:
    from qiskit.circuit.library import get_standard_gate_name_mapping
    gates = get_standard_gate_name_mapping()
    qc = QuantumCircuit(n)
    for name, angs, qs in seg.ops:
        qc.append(gates[name].base_class(*angs), qs)
    return qc


def segment_deviation(a: QuantumCircuit, b: QuantumCircuit) -> float:
    """The largest deviation, up to a phase per segment, between aligned unitary segments;
    NaN above 20 qubits."""
    if a.num_qubits > 20:
        return float("nan")
    sa, na, _ = split_segments(a)
    sb, nb, _ = split_segments(b)
    assert len(sa) == len(sb) and [x.operation.name for x in na] == [y.operation.name for y in nb]
    states = _states(a.num_qubits)
    dev = 0.0
    for x, y in zip(sa, sb):
        if not x.ops and not y.ops:
            continue
        cx_, cy = _segment(a.num_qubits, x), _segment(b.num_qubits, y)
        for v in states:
            u, w = v.evolve(cx_).data, v.evolve(cy).data
            ph = cmath.phase(np.vdot(w, u))
            dev = max(dev, float(np.abs(u - cmath.exp(-1j * ph) * w).max()))
    return dev


# --------------------------------------------------------------------------- main

def main(args: list[str]) -> None:
    import qiskit
    import qrisp

    check = False
    out_name = "results.tsv"
    if args[:1] == ["--check"]:
        check, args = True, args[1:]
    if len(args) >= 2 and args[0] == "--out":
        out_name, args = args[1], args[2:]
    names = args or list(PROGRAMS)
    vc = VerifiedCompiler(level="2r", check=check)
    load_avg = os.getloadavg()[0]
    header = ["circuit", "qubits", "classical", "cx_in", "ours_cx", "qiskit_cx", "ours_depth2",
              "qiskit_depth2", "ours_gates", "qiskit_gates", "ours_ms", "qiskit_ms", "qrisp_ms",
              "ours_dev", "qiskit_dev", "qiskit_perm", "qiskit_ne_cx", "qiskit_ne_gates", "eps"]
    pm_ne = no_elide_pass_manager()
    print("\t".join(header), flush=True)
    rows = []
    for name in names:
        t0 = time.perf_counter()
        obj, kw = PROGRAMS[name]()
        qin = to_qiskit(obj, kw)
        t_qrisp = time.perf_counter() - t0
        t_ours, t_qk = [], []
        for _ in range(REPEAT):
            t0 = time.perf_counter()
            ours = vc.compile(qin)
            t_ours.append(time.perf_counter() - t0)
            rep = vc.last_report
            if not rep.optimized:
                break
            t0 = time.perf_counter()
            qk = transpile(qin, basis_gates=BASIS, optimization_level=3, seed_transpiler=0)
            t_qk.append(time.perf_counter() - t0)
        if not rep.optimized:
            r = [name, qin.num_qubits, "-", figures(qin)[0], f"refused: {rep.reason}"]
            print("\t".join(map(str, r)), flush=True)
            rows.append(r)
            continue
        classical = not rep.unitary
        if classical:
            ours_dev, qk_dev = f"{segment_deviation(qin, ours):.1e}", "-"
        else:
            ours_dev, qk_dev = f"{deviation(qin, ours):.1e}", f"{deviation(qin, qk):.1e}"
        (ocx, od2, og), (qcx, qd2, qg) = figures(ours), figures(qk)
        eps = "unchecked" if rep.eps is None else f"{rep.eps:.1e}"
        # the CX count of the input as catq-compile imports it (cp, cz, swap, ccx lowered)
        cx_in = sum(int(row.split()[2]) for row in rep.rows)
        ne = pm_ne.run(qin)
        assert classical or qin.num_qubits > 10 or Operator(qin).equiv(Operator(ne))
        necx, _, neg = figures(ne)
        r = [name, qin.num_qubits, "yes" if classical else "no", cx_in, ocx, qcx,
             od2, qd2, og, qg, f"{min(t_ours) * 1e3:.1f}", f"{min(t_qk) * 1e3:.1f}",
             f"{t_qrisp * 1e3:.0f}", ours_dev, qk_dev, permuted(qk), necx, neg, eps]
        print("\t".join(map(str, r)), flush=True)
        rows.append(r)
    vc.close()
    os.makedirs(OUT_DIR, exist_ok=True)
    with open(os.path.join(OUT_DIR, out_name), "w") as f:
        f.write(f"# qrisp {qrisp.__version__ if hasattr(qrisp, '__version__') else _version('qrisp')}"
                f", qiskit {qiskit.__version__}, catq-compile level 2r{' --check' if check else ''}"
                f"; load average {load_avg:.2f} (taken under load), best of {REPEAT}, "
                f"{time.strftime('%Y-%m-%d %H:%M %Z')}\n")
        f.write("\t".join(header) + "\n")
        for r in rows:
            f.write("\t".join(map(str, r)) + "\n")


def _version(pkg: str) -> str:
    from importlib.metadata import version
    return version(pkg)


if __name__ == "__main__":
    main(sys.argv[1:])
