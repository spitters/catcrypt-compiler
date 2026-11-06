"""catq-compile (the verified Lean compiler of the Qrunch bridge) against Qiskit
transpile(optimization_level=3), both into the basis {rx, ry, rz, cx, p}, on OpenQASM 2 files.

Ours is `lake exe catq-compile` (CatCrypt/Quantum/Benchmark/QrunchCompile.lean), the
reference is Qiskit. Per file, interleaved, best of REPEAT:
  ours_ms      wall time of one `catq-compile --serve` request (file read, compile, write),
               measured from Python around the request line
  ours_core_ms the compile time the executable reports (import, Level 2, KAK, ZYZ, print)
  ours_proc_ms wall time of one `catq-compile <in> <out>` process, start-up included
  qiskit_ms    qasm2.load + transpile(optimization_level=3, basis above, seed 0)
and for both outputs, in the same basis: CX count, two-qubit depth, gate count, and
equality with the input (Operator up to 10 qubits, else four random statevectors), with
the phase catq-compile reports applied to ours and, for equality only, its output permutation
(appended as swaps; `ours_perm` says whether it is not the identity).

usage: cd bridge && uv run python -I ../bench/qrunch/compare.py [--check] [--out NAME.tsv]
       [FILE.qasm ...] (default: bench/qasm/qsynth/*.qasm); writes bench/qrunch/results.tsv or
       NAME.tsv; a file catq-compile refuses gets a row with its answer line; `--check` runs
       level 2r behind the verified checker (`catq-compile --check`)
"""
from __future__ import annotations

import glob
import os
import subprocess
import sys
import tempfile
import time
from fractions import Fraction

import numpy as np
from qiskit import QuantumCircuit, qasm2, transpile
from qiskit.circuit.library import CCZGate
from qiskit.quantum_info import Operator, Statevector, random_statevector

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "bridge"))
from catq.compiler import PERM_FIELD, append_swaps, parse_perm, swap_network  # noqa: E402
EXE = os.path.join(ROOT, ".lake", "build", "bin", "catq-compile")
BASIS = ["rx", "ry", "rz", "cx", "p"]
REPEAT = 5
PHASE_FIELD = 12  # the index of <phase> on the answer line of catq-compile
LEGACY = qasm2.LEGACY_CUSTOM_INSTRUCTIONS + (
    qasm2.CustomInstruction("ccz", 0, 3, CCZGate, builtin=True),)


def load(path: str) -> QuantumCircuit:
    """The circuit of an OpenQASM 2 file (qelib1 with Qiskit's legacy table and `ccz`), its
    final measurements and barriers removed (they are the identity on the unitary)."""
    qc = qasm2.load(path, custom_instructions=LEGACY)
    qc.remove_final_measurements(inplace=True)
    return qc


def figures(qc: QuantumCircuit) -> tuple[int, int, int]:
    ops = qc.count_ops()
    depth2 = qc.depth(lambda ins: ins.operation.num_qubits == 2)
    return int(ops.get("cx", 0)), depth2, qc.size()


def deviation(a: QuantumCircuit, b: QuantumCircuit) -> float:
    """max |A - B| entrywise (Operator) or over four statevectors; NaN above 20 qubits
    (not checked)."""
    if a.num_qubits > 20:
        return float("nan")
    if a.num_qubits <= 10:
        return float(np.abs(Operator(a).data - Operator(b).data).max())
    dev = 0.0
    for s in range(4):
        v = Statevector(random_statevector(2 ** a.num_qubits, seed=s))
        dev = max(dev, float(np.abs(v.evolve(a).data - v.evolve(b).data).max()))
    return dev


def main(args: list[str]) -> None:
    out_name = "results.tsv"
    flag = ""
    if args[:1] == ["--check"]:
        flag, args = " --check", args[1:]
    if len(args) >= 2 and args[0] == "--out":
        out_name, args = args[1], args[2:]
    paths = args or sorted(glob.glob(os.path.join(ROOT, "bench", "qasm", "qsynth", "*.qasm")))
    server = subprocess.Popen([EXE, "--serve"], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                              text=True, bufsize=1)
    load_avg = os.getloadavg()[0]
    rows = []
    header = ["circuit", "qubits", "cx_in", "ours_cx", "qiskit_cx", "ours_depth2", "qiskit_depth2",
              "ours_gates", "qiskit_gates", "ours_ms", "ours_core_ms", "ours_proc_ms", "qiskit_ms",
              "ours_dev", "qiskit_dev", "ours_perm"]
    print("\t".join(header), flush=True)
    with tempfile.TemporaryDirectory(prefix="qrunch-bench-") as wd:
        for path in paths:
            name = os.path.basename(path)[:-5]
            out = os.path.join(wd, name + ".out.qasm")
            src = load(path)
            t_ours, t_core, t_proc, t_qk = [], [], [], []
            refused = None
            for _ in range(REPEAT):
                t0 = time.perf_counter()
                server.stdin.write(f"{path} {out} 2r{flag}\n")
                server.stdin.flush()
                row = server.stdout.readline().split()
                t_ours.append(time.perf_counter() - t0)
                if row[0] != "ok":
                    refused = " ".join(row)
                    break
                t_core.append(int(row[6]) / 1e6)
                t0 = time.perf_counter()
                subprocess.run([EXE, path, out + ".p", "2r", *flag.split()], check=True,
                               capture_output=True)
                t_proc.append(time.perf_counter() - t0)
                t0 = time.perf_counter()
                qk = transpile(load(path), basis_gates=BASIS, optimization_level=3,
                               seed_transpiler=0)
                t_qk.append(time.perf_counter() - t0)
            if refused is not None:
                r = [name, src.num_qubits, figures(src)[0], refused]
                print("\t".join(map(str, r)), flush=True)
                rows.append(r)
                continue
            ours = load(out)
            ours.global_phase += float(Fraction(row[PHASE_FIELD]))
            # the output permutation of swap elision, applied for the deviation only (Qiskit's
            # level 3 elides swaps into its layout in the same way)
            perm = parse_perm(row[PERM_FIELD])
            ours_net = ours.copy()
            append_swaps(ours_net, swap_network(perm))
            (ocx, od2, og), (qcx, qd2, qg) = figures(ours), figures(qk)
            r = [name, src.num_qubits, figures(src)[0], ocx, qcx, od2, qd2, og, qg,
                 f"{min(t_ours) * 1e3:.1f}", f"{min(t_core) * 1e3:.1f}",
                 f"{min(t_proc) * 1e3:.1f}", f"{min(t_qk) * 1e3:.1f}",
                 f"{deviation(src, ours_net):.1e}", f"{deviation(src, qk):.1e}",
                 "no" if perm == list(range(len(perm))) else "yes"]
            print("\t".join(map(str, r)), flush=True)
            rows.append(r)
    server.stdin.close()
    server.wait(timeout=10)
    with open(os.path.join(HERE, out_name), "w") as f:
        f.write(f"# load average {load_avg:.2f}, best of {REPEAT}, "
                f"{time.strftime('%Y-%m-%d %H:%M %Z')}\n")
        f.write("\t".join(header) + "\n")
        for r in rows:
            f.write("\t".join(map(str, r)) + "\n")


if __name__ == "__main__":
    main(sys.argv[1:])
