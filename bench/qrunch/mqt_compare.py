"""MQT Bench (the Munich Quantum Toolkit benchmark suite) through catq-compile (the verified
Lean compiler of the Qrunch bridge, via `catq.compiler.VerifiedCompiler`) against Qiskit
transpile(optimization_level=3), both into the basis {rx, ry, rz, cx, p}.

Each circuit is MQT Bench's target-independent level (`get_benchmark(name,
BenchmarkLevel.INDEP, size)`: the algorithm transpiled by Qiskit at MQT's default level 2,
parameters bound by MQT to uniform angles in [0, 2π) from `numpy.random.default_rng(10)`,
`graphstate` with `seed=10`), unrolled by `transpile(optimization_level=0)` into the
statements `catq.qasm_io` lowers (MQT's composite gates `MAJ`, `qft_dg`, `rzz`, `mcphase`, ...
have no qelib1 meaning the importer reads), its final measurements removed. That one circuit
is the input of both compilers. Per family the size is the valid `circuit_size` nearest to
each requested size (default 5, 8, 12, 16), each size once. One run per circuit (no
repetition; the times are rough), in one process:
  ours_ms      `VerifiedCompiler(level="2r", check=True).compile` (segmentation, printing, one
               `catq-compile --serve --check` request per segment, reading back)
  ours_core_ms the compile time catq-compile reports, summed over the segments
  qiskit_ms    transpile(optimization_level=3, basis above, seed 0)
and for both outputs, in that basis: CX count, two-qubit depth and gate count (measurements,
resets and barriers not counted), and the deviation from the input: for a unitary circuit max
|A - B| entrywise, over the whole operator (`check` = op: up to 12 qubits while 4^n times the
gates of the four circuits is at most OPERATOR_WORK) or over four random statevectors
(`check` = sv4; one, sv1, when 4·2^n times those gates exceeds STATE_WORK; NaN above 20
qubits), ours with its phase and its restoring swaps, Qiskit's
through its layout (`Operator.from_circuit`'s reading), all evolved gate by gate (`evolve`,
which agrees with `Operator` to 1e-15 on the small rows); for a circuit with classical
instructions (`check` = seg: `dynamic_qft`, `ghz_dynamic`, `iqpe`, the error-correction
codes) the largest deviation of a unitary segment from its input up to a phase over four
random statevectors, for ours only (Qiskit moves gates across measurements: `-`). As in
compare.py, ours_cx, ours_depth2 and ours_gates do not count
the swaps (three cx each) that `VerifiedCompiler` appends to undo the output permutation of
swap elision; `ours_perm` says whether there was one. `cx_in` is the CX count of the input
translated into the basis above without optimization (`transpile(optimization_level=0)`); CX
inside `if_else` bodies are not counted there or on either output, where an `if_else` counts
as one gate. The `ours_lay_*`
columns are those of `VerifiedCompiler(level="2r", check=True, permutation="layout")`: no
swap appended, the permutation in the output's `final_layout`, the deviation through
`Operator.from_circuit` (unitary rows) or `CompileReport.layouts` (the others). A circuit
catq-compile refuses or that does not finish within `--timeout` seconds gets a row with the
reason in `ours_cx`.

usage: cd bridge && uv sync --extra mqt && uv run python -I ../bench/qrunch/mqt_compare.py
       [--append] [--sizes 5,8,12,16] [--timeout 300] [--out NAME.tsv] [FAMILY ...]
       writes bench/qrunch/mqt/results.tsv or NAME.tsv row by row (default: every MQT Bench
       family; `--append` adds rows to an existing file); the last column is the load average
       when the row was written
"""
from __future__ import annotations

import cmath
import importlib.metadata
import os
import sys
import threading
import time

import numpy as np
from qiskit import QuantumCircuit, transpile
from qiskit.circuit.library import get_standard_gate_name_mapping
from qiskit.quantum_info import Statevector, random_statevector

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "bridge"))
from catq.compiler import VerifiedCompiler, append_swaps, swap_network  # noqa: E402
from catq.qasm_io import ANNOTATION, IDENTITY, STATEMENTS, split_segments  # noqa: E402

BASIS = ["rx", "ry", "rz", "cx", "p"]
NOT_GATES = {"measure", "reset", "barrier"}
OUT_DIR = os.path.join(HERE, "mqt")
OPERATOR_MAX = 12
# 4^n times the gates of the four circuits evolved; above it the operator check (about
# 0.5 s per gate at 12 qubits on this machine) gives way to four statevectors
OPERATOR_WORK = 2 * 10 ** 9
# the same for four statevectors (4 * 2^n times the gates); above it, one statevector
STATE_WORK = 6 * 10 ** 9
STATE_MAX = 20
KWARGS = {"graphstate": {"seed": 10}}


def figures(qc: QuantumCircuit) -> tuple[int, int, int]:
    ops = qc.count_ops()
    depth2 = qc.depth(lambda ins: ins.operation.num_qubits == 2)
    gates = sum(v for k, v in ops.items() if k not in NOT_GATES)
    return int(ops.get("cx", 0)), depth2, gates


def _states(n: int):
    return [Statevector(random_statevector(2 ** n, seed=s)) for s in range(4)]


def _unpermute(data: np.ndarray, b: QuantumCircuit) -> np.ndarray:
    """Columns of states on the wires of `b` read through the output permutation of
    `b.layout` (for a matrix of columns, `Operator.from_circuit`'s reading)."""
    if b.layout is None:
        return data
    p = b.layout.final_index_layout(filter_ancillas=True)
    n = len(p)
    t = data.reshape((2,) * n + (data.shape[1],))
    return t.transpose([n - 1 - p[n - 1 - k] for k in range(n)] + [n]).reshape(data.shape)


def evolve(qc: QuantumCircuit, cols: np.ndarray) -> np.ndarray:
    """`U(qc) @ cols` for a unitary circuit, gate by gate on the tensor of `cols`, in Qiskit's
    little-endian convention (with `cols` the identity, `Operator(qc).data`; Qiskit's own
    `Operator` composes 4^n tensors and takes 100 s for 171 gates on 12 qubits)."""
    n = qc.num_qubits
    t = cols.reshape((2,) * n + (cols.shape[1],))
    cache: dict = {}
    for ins in qc.data:
        op = ins.operation
        if op.name in ANNOTATION or op.name in IDENTITY:
            continue
        key = (op.name, tuple(float(x) for x in op.params))
        if key not in cache:
            k = op.num_qubits
            cache[key] = np.asarray(op.to_matrix(), dtype=complex).reshape((2,) * (2 * k))
        m = cache[key]
        k = m.ndim // 2
        qs = [qc.find_bit(q).index for q in ins.qubits]
        # matrix axes (out_{k-1}, ..., out_0, in_{k-1}, ..., in_0); qubit q is axis n - 1 - q
        axes = [n - 1 - qs[j] for j in reversed(range(k))]
        t = np.moveaxis(np.tensordot(m, t, axes=(list(range(k, 2 * k)), axes)),
                        list(range(k)), axes)
    return (t * cmath.exp(1j * float(qc.global_phase))).reshape(cols.shape)


def probe(n: int, check: str) -> np.ndarray:
    """The identity (`check` = op) or one or four random statevectors (sv1, sv4), as
    columns."""
    if check == "op":
        return np.eye(2 ** n, dtype=complex)
    k = 1 if check == "sv1" else 4
    return np.stack([random_statevector(2 ** n, seed=s).data for s in range(k)], axis=1)


def deviation(a_cols: np.ndarray | None, probe_cols: np.ndarray, b: QuantumCircuit) -> float:
    """max |A - B| over the columns `a_cols = evolve(a, probe_cols)` (`b` through its
    layout); NaN when `a_cols` is None (above STATE_MAX qubits)."""
    if a_cols is None:
        return float("nan")
    return float(np.abs(a_cols - _unpermute(evolve(b, probe_cols), b)).max())


def _segment(n: int, seg) -> QuantumCircuit:
    gates = get_standard_gate_name_mapping()
    qc = QuantumCircuit(n)
    for name, angs, qs in seg.ops:
        qc.append(gates[name].base_class(*angs), qs)
    return qc


def segment_deviation(a: QuantumCircuit, b: QuantumCircuit, layouts: list[list[int]]) -> float:
    """The largest deviation, up to a phase per segment, between aligned unitary segments,
    segment `i` of `b` read through the wire layouts `layouts[i]` before it and
    `layouts[i + 1]` after it (`CompileReport.layouts`); NaN above STATE_MAX qubits."""
    if a.num_qubits > STATE_MAX:
        return float("nan")
    sa, na, _ = split_segments(a)
    sb, nb, _ = split_segments(b)
    assert len(sa) == len(sb) and [x.operation.name for x in na] == [y.operation.name for y in nb]
    n = b.num_qubits
    states = _states(n)
    dev = 0.0
    for i, (x, y) in enumerate(zip(sa, sb)):
        if not x.ops and not y.ops:
            continue
        cx_ = _segment(n, x)
        cy = QuantumCircuit(n)
        append_swaps(cy, list(reversed(swap_network(layouts[i]))))
        cy.compose(_segment(n, y), inplace=True)
        append_swaps(cy, swap_network(layouts[i + 1]))
        for v in states:
            u, w = v.evolve(cx_).data, v.evolve(cy).data
            # u = e^{i ph} w makes vdot(w, u) = e^{i ph}
            ph = cmath.phase(np.vdot(w, u))
            dev = max(dev, float(np.abs(u - cmath.exp(1j * ph) * w).max()))
    return dev


def instances(families: list[str], sizes: list[int]):
    """(family, circuit_size, circuit) for each family and each requested size: the valid
    `circuit_size` nearest to it (within 6; ties to the smaller), each size once."""
    from mqt.bench import BenchmarkLevel, get_benchmark
    for fam in families:
        done: set[int] = set()
        for want in sizes:
            for c in sorted(range(max(2, want - 6), want + 7), key=lambda c: (abs(c - want), c)):
                try:
                    qc = get_benchmark(fam, BenchmarkLevel.INDEP, c, **KWARGS.get(fam, {}))
                except ValueError:
                    continue
                if c not in done:
                    done.add(c)
                    yield fam, c, qc
                break
            else:
                yield fam, want, None


def lowered(qc: QuantumCircuit) -> QuantumCircuit:
    """`qc` unrolled into the statements `catq.qasm_io` lowers, final measurements removed."""
    out = transpile(qc, basis_gates=sorted(STATEMENTS), optimization_level=0)
    out.remove_final_measurements(inplace=True)
    return out


class Watched:
    """A `VerifiedCompiler` whose `catq-compile` process is killed after `timeout` seconds;
    one process serves both permutation modes (the mode only shapes the Python side)."""

    def __init__(self, timeout: float):
        self.vc = VerifiedCompiler(level="2r", check=True)
        self.timeout = timeout

    def compile(self, qc: QuantumCircuit, permutation: str):
        self.vc.permutation = permutation
        fired = []

        def kill():
            srv = self.vc._server
            if srv is not None and srv.proc.poll() is None:
                fired.append(True)
                srv.proc.kill()
        timer = threading.Timer(self.timeout, kill)
        timer.start()
        try:
            out = self.vc.compile(qc)
        finally:
            timer.cancel()
        rep = self.vc.last_report
        if fired:
            rep.reason = f"timeout after {self.timeout:.0f} s"
        if self.vc._server is not None and self.vc._server.proc.poll() is not None:
            self.vc._server = None
        return out, rep

    def close(self):
        self.vc.close()


def main(args: list[str]) -> None:
    out_name, sizes, timeout, append = "results.tsv", [5, 8, 12, 16], 300.0, False
    while args[:1] and args[0].startswith("--"):
        if args[0] == "--append":
            append, args = True, args[1:]
            continue
        flag, val, args = args[0], args[1], args[2:]
        if flag == "--out":
            out_name = val
        elif flag == "--sizes":
            sizes = [int(s) for s in val.split(",")]
        elif flag == "--timeout":
            timeout = float(val)
        else:
            raise SystemExit(f"unknown flag {flag}")
    from mqt.bench.benchmarks import get_available_benchmark_names
    families = args or list(get_available_benchmark_names())
    header = ["family", "size", "circuit", "qubits", "cx_in", "ours_cx", "qiskit_cx",
              "ours_depth2", "qiskit_depth2", "ours_gates", "qiskit_gates", "ours_ms",
              "ours_core_ms", "qiskit_ms", "ours_dev", "qiskit_dev", "check", "ours_perm",
              "ours_lay_cx", "ours_lay_gates", "ours_lay_dev"]
    comp = Watched(timeout)
    os.makedirs(OUT_DIR, exist_ok=True)
    out_file = open(os.path.join(OUT_DIR, out_name), "a" if append else "w")
    if not append:
        out_file.write(f"# mqt.bench {importlib.metadata.version('mqt.bench')}, qiskit "
                       f"{importlib.metadata.version('qiskit')}, level indep, one run per "
                       f"circuit, {time.strftime('%Y-%m-%d %H:%M %Z')}\n")
        out_file.write("\t".join(header + ["load_avg"]) + "\n")
    print("\t".join(header), flush=True)

    class _Rows(list):
        def append(self, r):
            line = "\t".join(map(str, list(r) + ["-"] * (len(header) - len(r))))
            print(line, flush=True)
            out_file.write(line + f"\t{os.getloadavg()[0]:.1f}\n")
            out_file.flush()
    rows = _Rows()
    for fam, size, qc in instances(families, sizes):
        name = f"{fam}_n{size}"
        if qc is None:
            r = [fam, size, name, "-", "-", f"no instance within 6 of size {size}"]
            rows.append(r)
            continue
        qin = lowered(qc)
        n = qin.num_qubits
        out, rep = comp.compile(qin, "swaps")
        if not rep.optimized:
            r = [fam, size, name, n, "-", f"refused: {rep.reason}"]
            rows.append(r)
            continue
        t0 = time.perf_counter()
        qk = transpile(qin, basis_gates=BASIS, optimization_level=3, seed_transpiler=0)
        t_qk = time.perf_counter() - t0
        cx_in = figures(transpile(qin, basis_gates=BASIS, optimization_level=0))[0]
        core_ms = sum(int(row.split()[6]) for row in rep.rows) / 1e3
        # the figures without the restoring swaps, as compare.py counts them
        bare = out.copy_empty_like()
        for ins in out.data[:len(out.data) - 3 * rep.swaps_appended]:
            bare.append(ins)
        perm = "no" if rep.final_permutation == list(range(n)) else "yes"
        lay, lrep = comp.compile(qin, "layout")
        if rep.unitary:
            work = 4 ** n * sum(c.size() for c in (qin, out, qk, lay))
            check = ("op" if n <= OPERATOR_MAX and work <= OPERATOR_WORK
                     else "-" if n > STATE_MAX
                     else "sv4" if 4 * 2 ** n * (work // 4 ** n) <= STATE_WORK else "sv1")
            pc = probe(n, check) if n <= STATE_MAX else None
            a_cols = evolve(qin, pc) if pc is not None else None
            ours_dev = f"{deviation(a_cols, pc, out):.1e}"
            qk_dev = f"{deviation(a_cols, pc, qk):.1e}"
            lay_dev = (f"{deviation(a_cols, pc, lay):.1e}" if lrep.optimized else None)
            del pc, a_cols
        else:
            ours_dev = f"{segment_deviation(qin, out, rep.layouts):.1e}"
            qk_dev, check = "-", "seg"
            lay_dev = (f"{segment_deviation(qin, lay, lrep.layouts):.1e}" if lrep.optimized
                       else None)
        if lrep.optimized:
            lcx, _, lg = figures(lay)
            lay_cols = [lcx, lg, lay_dev]
        else:
            lay_cols = ["-", "-", f"refused: {lrep.reason}"]
        (ocx, od2, og), (qcx, qd2, qg) = figures(bare), figures(qk)
        r = [fam, size, name, n, cx_in, ocx, qcx, od2, qd2, og, qg,
             f"{rep.seconds * 1e3:.1f}", f"{core_ms:.1f}", f"{t_qk * 1e3:.1f}",
             ours_dev, qk_dev, check, perm, *lay_cols]
        rows.append(r)
    comp.close()
    out_file.close()


if __name__ == "__main__":
    main(sys.argv[1:])
