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
not; `qiskit_ne_cx` and `qiskit_ne_gates` are its counts with that pass removed. The
`ours_lay_*` columns are those of `VerifiedCompiler(level="2r", permutation="layout")` on the
same input (run once, not timed), which returns the output permutation of swap elision in the
output's `final_layout` instead of appending swaps; `ours_lay_dev` reads it through
`Operator.from_circuit` (unitary rows) or through `CompileReport.layouts` (`*_mcm` rows).

With `--tutorials` the programs are those of Qrisp's tutorials (`TUTORIALS`), each run once
(the times are rough), Operator up to 12 qubits, written to results-tutorials.tsv; a program
Qrisp cannot build gets a row with the exception. Above SV_FAST (20) and up to SV_MAX (25)
qubits the deviation is taken over two random states with `_simulate` (numba, in place, one
state at a time: 2^n complex amplitudes are 0.5 GB at 25 qubits); QRISP_COMPARE_THREADS sets
its threads (default 4).

usage: cd bridge && uv sync --extra qrisp && uv run python -I ../bench/qrunch/qrisp_compare.py
       [--tutorials] [--check] [--out NAME.tsv] [CIRCUIT ...]; writes
       bench/qrunch/qrisp/results.tsv, results-tutorials.tsv or NAME.tsv
"""
from __future__ import annotations

import cmath
import os
import resource
import sys
import time

import networkx as nx
import numpy as np
from qiskit import QuantumCircuit, transpile
from qiskit.quantum_info import Operator, Statevector, random_statevector

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "bridge"))
from catq import VerifiedCompiler, append_swaps, swap_network  # noqa: E402
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


# ------------------------------------------------------------ programs of Qrisp's tutorials
# (documentation/source/general/tutorial/ of github.com/eclipse-qrisp/Qrisp, code taken from
# the notebooks; `--tutorials` runs these once each into results-tutorials.tsv)

def _tsp_parts(city_amount=4):
    """The permutation preparation and the QPE route-distance evaluation of the TSP tutorial."""
    from qrisp import QPE, QuantumArray, QuantumFloat, as_hamiltonian, demux, invert, lifted

    dist = np.array([[0, 0.25, 0.125, 0.5], [0.25, 0, 0.625, 0.375],
                     [0.125, 0.625, 0, 0.75], [0.5, 0.375, 0.75, 0]]) / city_amount

    def swap_to_front(qa, index):
        with invert():
            demux(qa[0], index, qa, permit_mismatching_size=True)

    def eval_perm(perm_specifiers):
        qa = QuantumArray(QuantumFloat(int(np.ceil(np.log2(city_amount)))), city_amount)
        qa[:] = np.arange(city_amount)
        for i in range(city_amount - 1):
            swap_to_front(qa[i:], perm_specifiers[i])
        return qa

    def create_perm_specifiers():
        return [QuantumFloat(int(np.ceil(np.log2(city_amount - i))))
                for i in range(city_amount - 1)]

    @as_hamiltonian
    def trip_distance(i, j, iter=1):
        return dist[i, j] * 2 * np.pi * iter

    def phase_apply_summed_distance(itinerary, iter=1):
        n = len(itinerary)
        for i in range(n):
            trip_distance(itinerary[i], itinerary[(i + 1) % n], iter=iter)

    @lifted
    def qpe_calc_perm_travel_distance(itinerary, precision):
        return QPE(itinerary, phase_apply_summed_distance, precision=precision, iter_spec=True)

    return eval_perm, create_perm_specifiers, qpe_calc_perm_travel_distance


def tsp():
    """TSP tutorial, 4 cities: Grover search over the permutation specifiers (5 qubits) with the
    oracle `eval_distance_threshold` (QPE route distance, precision 5, threshold 0.4), one
    Grover iteration (`winner_state_amount` as in the tutorial), no final measurement."""
    from math import factorial

    from qrisp import auto_uncompute, z
    from qrisp.grover import grovers_alg

    eval_perm, create_perm_specifiers, qpe_dist = _tsp_parts()

    @auto_uncompute
    def eval_distance_threshold(perm_specifiers, precision, threshold):
        distance = qpe_dist(eval_perm(perm_specifiers), precision)
        z(distance <= threshold)

    ps = create_perm_specifiers()
    winners = (2 ** sum(qv.size for qv in ps) / factorial(4)) * 4 * 2
    grovers_alg(ps, eval_distance_threshold, kwargs={"threshold": 0.4, "precision": 5},
                winner_state_amount=winners)
    return ps[0].qs, {}


def _backtracking_tree(accept, reject, depth, branch_size, subspace_optimization, precision):
    from qrisp import QuantumFloat
    from qrisp.quantum_backtracking import QuantumBacktrackingTree

    tree = QuantumBacktrackingTree(depth, branch_qv=QuantumFloat(branch_size), accept=accept,
                                   reject=reject, subspace_optimization=subspace_optimization)
    tree.init_node([])
    return tree.estimate_phase(precision=precision).qs


def backtrack_binary():
    """Sudoku tutorial, first part: the binary tree of depth 3 with `accept` marking the path
    [1,1,1] and `reject` cutting [0] at height 2; `estimate_phase(precision=3)`."""
    from qrisp import auto_uncompute

    @auto_uncompute
    def accept(tree):
        return (tree.branch_qa[0] == 1) & (tree.branch_qa[1] == 1) & (tree.branch_qa[2] == 1)

    @auto_uncompute
    def reject(tree):
        return (tree.h == 2) & (tree.branch_qa[2] == 0)

    return _backtracking_tree(accept, reject, 3, 1, False, 3), {}


def sudoku():
    """Sudoku tutorial, final part: the 4x4 board with three empty fields, tree depth 4 over
    2-qubit branches, `subspace_optimization=True`, `estimate_phase(precision=3)`."""
    from qrisp import QuantumBool, QuantumDictionary, auto_uncompute, control, mcx

    board = np.array([[0, -1, 2, 3], [2, 3, 0, -1], [1, 0, 3, 2], [3, -1, 1, 0]])
    n_empty = int(np.count_nonzero(board == -1))

    def sudoku_to_graph():
        g, empty = nx.Graph(), []
        kind = lambda k, l: "qq" if board[k, l] == -1 else "cq"  # noqa: E731
        for i in range(4):
            for j in range(4):
                if board[i, j] != -1:
                    continue
                node = (i, j)
                empty.append(node)
                g.add_node(node)
                for k in range(4):
                    if k != j:
                        g.add_edge(node, (i, k), edge_type=kind(i, k))
                for k in range(4):
                    if k != i:
                        g.add_edge(node, (k, j), edge_type=kind(k, j))
                for k in range((i // 2) * 2, (i // 2) * 2 + 2):
                    for l in range((j // 2) * 2, (j // 2) * 2 + 2):
                        if (k, l) != node:
                            g.add_edge(node, (k, l), edge_type=kind(k, l))
        return g, empty

    def extract_comparisons():
        graph, empty = sudoku_to_graph()
        cq = {q: [] for q in range(n_empty)}
        qq = []
        for edge in graph.edges():
            if graph.get_edge_data(*edge)["edge_type"] == "qq":
                qq.append((empty.index(edge[0]), empty.index(edge[1])))
            elif board[edge[1]] == -1:
                cq[empty.index(edge[1])].append(board[edge[0]])
            else:
                cq[empty.index(edge[0])].append(board[edge[1]])
        return qq, cq

    def cq_eq_check(q_value, cl_values):
        if len(cl_values) == 0:
            return QuantumBool()
        qd = QuantumDictionary(return_type=QuantumBool())
        for value in [q_value.decoder(i) for i in range(2 ** q_value.size)]:
            qd[value] = value in cl_values
        return qd[q_value]

    def check_singular(q_assignments, h):
        qq, cq = extract_comparisons()
        qbls = []
        for i0, i1 in qq:
            with control(h[min(i0, i1)]):
                eq = q_assignments[i0] == q_assignments[i1]
            qbls.append(eq)
        for key, value in cq.items():
            with control(h[key]):
                eq = cq_eq_check(q_assignments[key], value)
            qbls.append(eq)
        valid = QuantumBool()
        mcx(qbls, valid, ctrl_state=0, method="balauca")
        return valid

    @auto_uncompute
    def accept(tree):
        return tree.h == 0

    @auto_uncompute
    def reject(tree):
        return check_singular(tree.branch_qa[1:], tree.h[1:]).flip()

    return _backtracking_tree(accept, reject, n_empty + 1, 2, True, 3), {}


def hhl():
    """HHL on the HHL tutorial's system A = [[3/8, 1/8], [1/8, 3/8]], b = (1, 1), with its
    Hamiltonian evolution (`QubitOperator.from_matrix(A).to_pauli().trotterization()`, t = -pi,
    one step), through the static `qrisp.algorithms.hhl.HHL` at precision 3; the eigenvalue
    inversion rotates the ancilla by 2 arcsin(1/k) on the QPE value k/8 (k = 1..7)."""
    from qrisp import QuantumFloat, prepare, ry
    from qrisp.algorithms.hhl import HHL
    from qrisp.operators import QubitOperator

    H = QubitOperator.from_matrix(np.array([[3 / 8, 1 / 8], [1 / 8, 3 / 8]])).to_pauli()

    def U(qf):
        H.trotterization()(qf, t=-np.pi, steps=1)

    def ev_inversion(res, anc):
        for k in range(1, 2 ** res.size):
            with res == k * 2.0 ** res.exponent:
                ry(2 * np.arcsin(1 / k), anc)

    qf = QuantumFloat(1)
    prepare(qf, np.array([1, 1]), reversed=True)
    return HHL(qf, U, ev_inversion, 3).qs, {}


def iqae_qmci():
    """QMCI tutorial: the state function of the integral of x^2 on [0, 1] (x in
    QuantumFloat(3, -3), y in QuantumFloat(6, -6)) followed by one amplitude-amplification
    iteration, the circuit of the round K = 3 of `IQAE` (`quantum_step` with k = 1)."""
    from qrisp import QuantumBool, QuantumFloat, amplitude_amplification, auto_uncompute, h, x, z

    @auto_uncompute
    def state_function(qf_x, qf_y, qbl):
        h(qf_x)
        h(qf_y)
        with qf_y < qf_x * qf_x:
            x(qbl)

    def oracle(*args):
        z(args[-1])

    qargs = [QuantumFloat(3, -3), QuantumFloat(6, -6), QuantumBool()]
    state_function(*qargs)
    amplitude_amplification(qargs, state_function, oracle, iter=1)
    return qargs[-1].qs, {}


def counting():
    """`quantum_counting` with its docstring's oracle (z on the last qubit) on a 4-qubit
    variable, precision 4 (the circuit before the measurement of the estimate)."""
    from qrisp import QuantumVariable, quantum_counting, z

    qv = QuantumVariable(4)
    quantum_counting(qv, lambda q: z(q[-1]), 4)
    return qv.qs, {}


TUTORIALS = {f.__name__: f for f in (tsp, backtrack_binary, sudoku, hhl, iqae_qmci, counting)}


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


SV_MAX = 25   # the statevector check runs up to this many qubits
SV_FAST = 20  # above this, `_simulate` (numba) instead of Statevector.evolve, two states
SIM_THREADS = int(os.environ.get("QRISP_COMPARE_THREADS", "4"))  # numba threads of `_simulate`
_KERNELS = None


def _kernels():
    """In-place numba kernels applying a 1-, 2- or 3-qubit matrix to a state (bit q of the
    index is qubit q; bit k of the matrix index is the k-th qubit argument), and the largest
    |u[i] - ph * w[map(i)]|, where map(i) = sum_j bit_j(i) << perm[j] reads `w` through an
    output permutation as `_unpermute` does."""
    global _KERNELS
    if _KERNELS is not None:
        return _KERNELS
    import numba
    from numba import njit, prange

    numba.set_num_threads(min(SIM_THREADS, numba.config.NUMBA_NUM_THREADS))

    @njit(inline="always")
    def ins(i, s):
        return ((i >> s) << (s + 1)) | (i & ((1 << s) - 1))

    @njit(parallel=True)
    def k1(psi, q, m):
        b = 1 << q
        for i in prange(psi.size >> 1):
            j = ins(i, q)
            x0, x1 = psi[j], psi[j | b]
            psi[j] = m[0, 0] * x0 + m[0, 1] * x1
            psi[j | b] = m[1, 0] * x0 + m[1, 1] * x1

    @njit(parallel=True)
    def k2(psi, qa, qb, m):
        s0, s1 = min(qa, qb), max(qa, qb)
        a, b = 1 << qa, 1 << qb
        for i in prange(psi.size >> 2):
            j = ins(ins(i, s0), s1)
            x0, x1, x2, x3 = psi[j], psi[j | a], psi[j | b], psi[j | a | b]
            psi[j] = m[0, 0] * x0 + m[0, 1] * x1 + m[0, 2] * x2 + m[0, 3] * x3
            psi[j | a] = m[1, 0] * x0 + m[1, 1] * x1 + m[1, 2] * x2 + m[1, 3] * x3
            psi[j | b] = m[2, 0] * x0 + m[2, 1] * x1 + m[2, 2] * x2 + m[2, 3] * x3
            psi[j | a | b] = m[3, 0] * x0 + m[3, 1] * x1 + m[3, 2] * x2 + m[3, 3] * x3

    @njit(parallel=True)
    def k3(psi, qs, offs, m):
        s = np.sort(qs)
        for i in prange(psi.size >> 3):
            j = ins(ins(ins(i, s[0]), s[1]), s[2])
            x0, x1, x2, x3 = psi[j], psi[j | offs[1]], psi[j | offs[2]], psi[j | offs[3]]
            x4, x5, x6, x7 = psi[j | offs[4]], psi[j | offs[5]], psi[j | offs[6]], psi[j | offs[7]]
            for r in range(8):
                psi[j | offs[r]] = (m[r, 0] * x0 + m[r, 1] * x1 + m[r, 2] * x2 + m[r, 3] * x3
                                    + m[r, 4] * x4 + m[r, 5] * x5 + m[r, 6] * x6
                                    + m[r, 7] * x7)

    @njit
    def chunk_diff(u, w, perm, ph, lo, hi):
        best = 0.0
        for i in range(lo, hi):
            k = 0
            for t in range(perm.size):
                k = k | (((i >> t) & 1) << perm[t])
            d = abs(u[i] - ph * w[k])
            if d > best:
                best = d
        return best

    @njit(parallel=True)
    def kdiff(u, w, perm, ph):
        chunks = 1024
        size = u.size // chunks
        out = np.zeros(chunks)
        for c in prange(chunks):
            out[c] = chunk_diff(u, w, perm, ph, c * size, (c + 1) * size)
        return out.max()

    _KERNELS = (k1, k2, k3, kdiff)
    return _KERNELS


def _embed(m: np.ndarray, pos: list[int], k: int) -> np.ndarray:
    """The matrix `m` on qubits `pos` (bit t of its index is qubit pos[t]) as a matrix on k
    qubits."""
    g = np.zeros((2 ** k, 2 ** k), dtype=np.complex128)
    mask = sum(1 << p for p in pos)
    for c in range(2 ** k):
        s = sum(((c >> p) & 1) << t for t, p in enumerate(pos))
        for r in range(2 ** len(pos)):
            g[(c & ~mask) | sum(((r >> t) & 1) << p for t, p in enumerate(pos)), c] = m[r, s]
    return g


def _fused_ops(qc: QuantumCircuit) -> list[tuple[list[int], np.ndarray]]:
    """The gates of `qc` as (qubits, matrix) fused greedily into blocks of at most three qubits
    (bit t of a block's matrix index is its t-th qubit). Blocks on disjoint qubits stay open
    together; a gate joins (and merges) the open blocks it touches when their qubits and its
    own number at most three, and otherwise those blocks are emitted and it opens a new one.
    An open block it does not touch acts on other qubits, so it commutes with the gate."""
    idx = {q: i for i, q in enumerate(qc.qubits)}
    out: list[tuple[list[int], np.ndarray]] = []
    open_: list[tuple[list[int], np.ndarray]] = []
    for ins in qc.data:
        if ins.operation.name == "barrier":
            continue
        qs = [idx[q] for q in ins.qubits]
        assert len(qs) <= 3 and not ins.clbits, ins.operation.name
        m = Operator(ins.operation).data
        hit = [b for b in open_ if set(b[0]) & set(qs)]
        rest = [b for b in open_ if not set(b[0]) & set(qs)]
        union = {q for b in hit for q in b[0]} | set(qs)
        if len(union) <= 3:
            block, mat = [], np.eye(1, dtype=np.complex128)
            for bq, bm in hit:  # disjoint blocks: their product is the Kronecker product
                block, mat = block + bq, np.kron(bm, mat)
        else:
            out.extend(hit)
            block, mat = [], np.eye(1, dtype=np.complex128)
        for q in qs:
            if q not in block:  # a new qubit of the block is its next (highest) bit
                block, mat = block + [q], np.kron(np.eye(2), mat)
        mat = _embed(m, [block.index(q) for q in qs], len(block)) @ mat
        open_ = rest + [(block, mat)]
    out.extend(open_)
    return [(b, np.ascontiguousarray(m)) for b, m in out]


def _simulate(qc: QuantumCircuit, psi: np.ndarray) -> np.ndarray:
    """`psi` evolved in place by `qc`, without its global phase."""
    k1, k2, k3, _ = _kernels()
    for qs, m in _fused_ops(qc):
        if len(qs) == 1:
            k1(psi, qs[0], m)
        elif len(qs) == 2:
            k2(psi, qs[0], qs[1], m)
        else:
            offs = np.array([sum(((r >> t) & 1) << qs[t] for t in range(3)) for r in range(8)])
            k3(psi, np.array(qs), offs, m)
    return psi


def _random_state(n: int, seed: int) -> np.ndarray:
    """A Haar-random state of n qubits (normalised complex Gaussian), built in place."""
    rng = np.random.default_rng(seed)
    psi = np.empty(2 ** n, dtype=np.complex128)
    psi.real = rng.standard_normal(2 ** n)
    psi.imag = rng.standard_normal(2 ** n)
    psi /= np.linalg.norm(psi)
    return psi


def _deviations_fast(a: QuantumCircuit, bs: list[QuantumCircuit], n_states: int = 2) -> list[float]:
    """`deviation(a, b)` for each `b` in `bs` over `n_states` random states, one state at a
    time: the state evolved by `a` is kept while each `b` evolves a fresh copy, which is freed
    before the next."""
    _, _, _, kdiff = _kernels()
    n = a.num_qubits
    devs = [0.0] * len(bs)
    for s in range(n_states):
        u = _simulate(a, _random_state(n, s))
        u *= cmath.exp(1j * a.global_phase)
        for t, b in enumerate(bs):
            w = _simulate(b, _random_state(n, s))
            perm = (np.arange(n) if b.layout is None
                    else np.array(b.layout.final_index_layout(filter_ancillas=True)))
            devs[t] = max(devs[t], float(kdiff(u, w, perm, cmath.exp(1j * b.global_phase))))
            del w
        del u
    return devs


def deviations(a: QuantumCircuit, bs: list[QuantumCircuit], op_max: int = 10) -> list[float]:
    """`deviation(a, b)` for each `b` in `bs`; above SV_FAST qubits through `_deviations_fast`,
    which evolves the input once per state for all of `bs`."""
    if SV_FAST < a.num_qubits <= SV_MAX:
        return _deviations_fast(a, bs)
    return [deviation(a, b, op_max) for b in bs]


def deviation(a: QuantumCircuit, b: QuantumCircuit, op_max: int = 10) -> float:
    """max |A - B| entrywise (Operator up to `op_max` qubits, through the output permutation
    of `b.layout`) or over four statevectors (two above SV_FAST qubits, `_deviations_fast`);
    NaN above SV_MAX qubits."""
    if a.num_qubits > SV_MAX:
        return float("nan")
    if a.num_qubits > SV_FAST:
        return _deviations_fast(a, [b])[0]
    if a.num_qubits <= op_max:
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


def segment_deviation(a: QuantumCircuit, b: QuantumCircuit,
                      layouts: list[list[int]] | None = None) -> float:
    """The largest deviation, up to a phase per segment, between aligned unitary segments,
    segment `i` of `b` read through the wire layouts `layouts[i]` before it and
    `layouts[i + 1]` after it (`CompileReport.layouts`; the identity when `None`); NaN above
    20 qubits."""
    if a.num_qubits > 20:
        return float("nan")
    sa, na, _ = split_segments(a)
    sb, nb, _ = split_segments(b)
    assert len(sa) == len(sb) and [x.operation.name for x in na] == [y.operation.name for y in nb]
    n = b.num_qubits
    layouts = layouts or [list(range(n))] * (len(sb) + 1)
    states = _states(a.num_qubits)
    dev = 0.0
    for i, (x, y) in enumerate(zip(sa, sb)):
        if not x.ops and not y.ops:
            continue
        cx_ = _segment(a.num_qubits, x)
        # input qubit q onto wire layouts[i][q], the segment, then back from layouts[i + 1]
        cy = QuantumCircuit(n)
        append_swaps(cy, list(reversed(swap_network(layouts[i]))))
        cy.compose(_segment(n, y), inplace=True)
        append_swaps(cy, swap_network(layouts[i + 1]))
        for v in states:
            u, w = v.evolve(cx_).data, v.evolve(cy).data
            ph = cmath.phase(np.vdot(w, u))
            # u = e^{i ph} w up to the deviation, ph = arg <w, u>
            dev = max(dev, float(np.abs(u - cmath.exp(1j * ph) * w).max()))
    return dev


# --------------------------------------------------------------------------- main

def main(args: list[str]) -> None:
    import qiskit
    import qrisp

    check = False
    out_name = "results.tsv"
    programs, repeat, op_max = PROGRAMS, REPEAT, 10
    if args[:1] == ["--tutorials"]:
        programs, repeat, op_max, args = TUTORIALS, 1, 12, args[1:]
        out_name = "results-tutorials.tsv"
    if args[:1] == ["--check"]:
        check, args = True, args[1:]
    if len(args) >= 2 and args[0] == "--out":
        out_name, args = args[1], args[2:]
    names = args or list(programs)
    vc = VerifiedCompiler(level="2r", check=check)
    vc_lay = VerifiedCompiler(level="2r", check=check, permutation="layout")
    load_avg = os.getloadavg()[0]
    header = ["circuit", "qubits", "classical", "cx_in", "ours_cx", "qiskit_cx", "ours_depth2",
              "qiskit_depth2", "ours_gates", "qiskit_gates", "ours_ms", "qiskit_ms", "qrisp_ms",
              "ours_dev", "qiskit_dev", "qiskit_perm", "qiskit_ne_cx", "qiskit_ne_gates", "eps",
              "ours_lay_cx", "ours_lay_depth2", "ours_lay_gates", "ours_lay_dev"]
    pm_ne = no_elide_pass_manager()
    # warm-up, so that a single run does not time the server start or Qiskit's first call
    warm = QuantumCircuit(2)
    warm.h(0)
    warm.cx(0, 1)
    vc.compile(warm)
    transpile(warm, basis_gates=BASIS, optimization_level=3, seed_transpiler=0)
    print("\t".join(header), flush=True)
    rows = []
    for name in names:
        t0 = time.perf_counter()
        try:
            obj, kw = programs[name]()
            qin = to_qiskit(obj, kw)
        except Exception as e:  # a program Qrisp cannot build gets a row with the reason
            r = [name, "-", "-", "-", f"qrisp failed: {type(e).__name__}: {e}"[:200]]
            print("\t".join(map(str, r)), flush=True)
            rows.append(r)
            continue
        t_qrisp = time.perf_counter() - t0
        t_ours, t_qk = [], []
        for _ in range(repeat):
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
        lay = vc_lay.compile(qin)
        lrep = vc_lay.last_report
        if classical:
            ours_dev, qk_dev = f"{segment_deviation(qin, ours, rep.layouts):.1e}", "-"
            lay_dev = segment_deviation(qin, lay, lrep.layouts) if lrep.optimized else None
        else:
            devs = deviations(qin, [ours, qk] + ([lay] if lrep.optimized else []), op_max)
            ours_dev, qk_dev = f"{devs[0]:.1e}", f"{devs[1]:.1e}"
            lay_dev = devs[2] if lrep.optimized else None
        (ocx, od2, og), (qcx, qd2, qg) = figures(ours), figures(qk)
        eps = "unchecked" if rep.eps is None else f"{rep.eps:.1e}"
        # the CX count of the input as catq-compile imports it (cp, cz, swap, ccx lowered)
        cx_in = sum(int(row.split()[2]) for row in rep.rows)
        ne = pm_ne.run(qin)
        assert classical or qin.num_qubits > op_max or Operator(qin).equiv(Operator(ne))
        necx, _, neg = figures(ne)
        if not lrep.optimized:
            lay_cols = ["-", "-", "-", f"refused: {lrep.reason}"]
        else:
            lay_cols = [*figures(lay), f"{lay_dev:.1e}"]
        r = [name, qin.num_qubits, "yes" if classical else "no", cx_in, ocx, qcx,
             od2, qd2, og, qg, f"{min(t_ours) * 1e3:.1f}", f"{min(t_qk) * 1e3:.1f}",
             f"{t_qrisp * 1e3:.0f}", ours_dev, qk_dev, permuted(qk), necx, neg, eps, *lay_cols]
        print("\t".join(map(str, r)), flush=True)
        rows.append(r)
    vc.close()
    vc_lay.close()
    os.makedirs(OUT_DIR, exist_ok=True)
    with open(os.path.join(OUT_DIR, out_name), "w") as f:
        f.write(f"# qrisp {qrisp.__version__ if hasattr(qrisp, '__version__') else _version('qrisp')}"
                f", qiskit {qiskit.__version__}, catq-compile level 2r{' --check' if check else ''}"
                f"; load average {load_avg:.2f} (taken under load), "
                f"{'best of ' + str(repeat) if repeat > 1 else 'one run'}, peak RSS "
                f"{resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 2 ** 20:.1f} GiB, "
                f"{time.strftime('%Y-%m-%d %H:%M %Z')}\n")
        f.write("\t".join(header) + "\n")
        for r in rows:
            f.write("\t".join(map(str, r)) + "\n")


def _version(pkg: str) -> str:
    from importlib.metadata import version
    return version(pkg)


if __name__ == "__main__":
    main(sys.argv[1:])
