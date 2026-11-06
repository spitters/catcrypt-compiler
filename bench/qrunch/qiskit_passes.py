"""Which passes of Qiskit's level-3 preset still lower catq-compile's output.

For each circuit of the four suites (Q-Synth, Nam, QASMBench small, the Qrisp programs of
`qrisp_compare.py`), catq-compile at level 2r is run to its fixed point: its output is fed back
until neither the CX count nor the gate count falls. On that output (the base) each pass of
`generate_preset_pass_manager(3, basis_gates=BASIS)` is run alone, followed by the preset's
translation stage into BASIS; so are the init stage, the optimization stage (Qiskit's do-while
loop with its minimum-point backtracking) and the whole preset without `ElidePermutations`.
`ConsolidateBlocks` runs with the `Split2QUnitaries` that follows it in the init stage.

`ElidePermutations` removes SWAP and permutation gates, which catq-compile's import lowers to
CX, so it is measured on the input instead: the input with its SWAPs elided is compiled by
catq-compile to its fixed point and compared with the base, through the output permutation.

Every output that differs from its input is checked against it up to a global phase:
`Operator.equiv` up to 10 qubits, the overlap |<u|w>| on one random statevector up to 20,
not checked above (`nosim`). numpy runs on two threads (the box is shared).

A pass that lowers the CX or gate count gets a second row, `<pass> +catq`: its output compiled
by catq-compile to its fixed point, which measures what catq-compile would reach with that pass
in its loop. The reverse direction: catq-compile, to its fixed point, on the output of the
preset without `ElidePermutations` run on the original input. Qiskit's outputs are handed to
catq-compile through `qasm2.dumps` (`Catq._write`, `snap`).

usage: cd bridge && uv run python -I ../bench/qrunch/qiskit_passes.py [--snap] [SUITE ...]
       (suites: qsynth nam qasmbench qrisp; default all); writes
       bench/qrunch/qiskit-passes/[snap-][SUITE-...-]{base,passes,reverse}.tsv
  --snap       the base is the fixed point after one `snap +catq` step (see below), so the
               rows measure what remains once the angles are snapped
  base.tsv     catq-compile's figures after one run and at its fixed point, runs to reach it
  passes.tsv   per circuit and pass: CX, two-qubit depth and gates after the pass and their
               differences from the base (negative = the pass lowers it), and the check
  reverse.tsv  Qiskit's output and catq-compile's fixed point on it
"""
from __future__ import annotations

import glob
import os

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "RAYON_NUM_THREADS"):
    os.environ.setdefault(_v, "2")
import subprocess
import sys
import tempfile
import time

import numpy as np
from qiskit import QuantumCircuit, qasm2
from qiskit.circuit.library import CCZGate, PermutationGate
from qiskit.quantum_info import Operator, Statevector, random_statevector
from qiskit.transpiler import PassManager, generate_preset_pass_manager
from qiskit.transpiler.passes import ElidePermutations

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "bridge"))
from catq import VerifiedCompiler  # noqa: E402
from catq.qasm_io import lower, split_segments  # noqa: E402

EXE = os.path.join(ROOT, ".lake", "build", "bin", "catq-compile")
BASIS = ["rx", "ry", "rz", "cx", "p"]
NOT_GATES = {"measure", "reset", "barrier"}
OUT_DIR = os.path.join(HERE, "qiskit-passes")
MAX_RUNS = 12
LEGACY = qasm2.LEGACY_CUSTOM_INSTRUCTIONS + (
    qasm2.CustomInstruction("ccz", 0, 3, CCZGate, builtin=True),)
# The Nam circuits are fetched by fetch-nam.sh into bench/qasm/nam of a checkout; the dev
# workspace keeps a copy beside this repository.
NAM_DIRS = [os.path.join(ROOT, "bench", "qasm", "nam"),
            os.path.join(os.path.dirname(ROOT), "SSProve-lean", "bench", "qasm", "nam")]


# --------------------------------------------------------------------------- figures, checks

def figures(qc: QuantumCircuit) -> tuple[int, int, int]:
    ops = qc.count_ops()
    depth2 = qc.depth(lambda ins: ins.operation.num_qubits == 2)
    gates = sum(v for k, v in ops.items() if k not in NOT_GATES)
    return int(ops.get("cx", 0)), depth2, gates


def _image(qc: QuantumCircuit):
    """The Operator of `qc` up to 10 qubits, else the image of one random statevector up to
    20; None above 20 qubits or with classical instructions."""
    n = qc.num_qubits
    if n > 20 or any(ins.clbits for ins in qc.data):
        return None
    if n <= 10:
        return Operator(qc)
    return Statevector(random_statevector(2 ** n, seed=0)).evolve(qc).data


def better(f: tuple[int, int, int], g: tuple[int, int, int]) -> bool:
    """Figures `f` improve on `g`: fewer CX, or as many CX and fewer gates."""
    return (f[0], f[2]) < (g[0], g[2])


def same_up_to_phase(a, b: QuantumCircuit) -> str:
    """`ok` or `FAIL` (up to a global phase), `nosim` above 20 qubits or with classical
    instructions; `a` is a circuit or its `_image`."""
    ia = _image(a) if isinstance(a, QuantumCircuit) else a
    ib = _image(b) if ia is not None else None
    if ia is None or ib is None:
        return "nosim"
    if isinstance(ia, Operator):
        return "ok" if ia.equiv(ib, atol=1e-8) else "FAIL"
    return "ok" if abs(np.vdot(ia, ib)) > 1 - 1e-8 else "FAIL"


def bare(qc: QuantumCircuit) -> QuantumCircuit:
    """`qc` without its layout, on qubits 0..n-1."""
    out = QuantumCircuit(qc.num_qubits, qc.num_clbits)
    out.compose(qc, inplace=True)
    out.global_phase = qc.global_phase
    return out


# --------------------------------------------------------------------------- catq-compile

class Catq:
    """One `catq-compile --serve` process; `fixpoint` feeds the output back until neither CX
    nor gate count falls."""

    def __init__(self, wd: str):
        self.wd = wd
        self.k = 0
        self.proc = subprocess.Popen(["prlimit", f"--as={4000 * 1024 * 1024}", EXE, "--serve"],
                                     stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True,
                                     bufsize=1, cwd=ROOT)
        self.vc = VerifiedCompiler(level="2r")

    def close(self) -> None:
        self.proc.stdin.close()
        self.proc.wait(timeout=10)
        self.vc.close()

    def _file(self, src: str) -> QuantumCircuit | None:
        self.k += 1
        out = os.path.join(self.wd, f"o{self.k}.qasm")
        self.proc.stdin.write(f"{src} {out} 2r\n")
        self.proc.stdin.flush()
        row = self.proc.stdout.readline().strip()
        if not row.startswith("ok"):
            return None
        qc = qasm2.load(out, custom_instructions=qasm2.LEGACY_CUSTOM_INSTRUCTIONS)
        qc.metadata = {"file": out}
        return qc

    def _write(self, qc: QuantumCircuit, snap: bool) -> str | None:
        """A file of `qc` in the statements catq-compile reads, when `qc` is one unitary
        segment: the bridge's printing (`qasm_io.lower`, every angle as its double), or with
        `snap` Qiskit's `qasm2.dumps`, which prints an angle within 1e-12 of a rational
        multiple of pi as that multiple (used on Qiskit's outputs, whose angles were exact
        multiples of pi in catq-compile's output before Qiskit turned them into doubles)."""
        segs, _, unitary = split_segments(qc)
        if not unitary or len(segs) != 1:
            return None
        self.k += 1
        path = os.path.join(self.wd, f"i{self.k}.qasm")
        with open(path, "w") as f:
            f.write(qasm2.dumps(qc) if snap else lower(qc.num_qubits, segs[0]))
        return path

    def once(self, src, snap: bool = False) -> QuantumCircuit | None:
        """One run on a file path or a circuit; the output of a file run keeps its file, so
        later runs read catq-compile's exact angles."""
        if isinstance(src, str):
            return self._file(src)
        if src.metadata and "file" in src.metadata:
            return self._file(src.metadata["file"])
        path = self._write(src, snap)
        if path is not None:
            return self._file(path)
        out = self.vc.compile(src)
        return out if self.vc.last_report.optimized else None

    def fixpoint(self, src, snap: bool = False
                 ) -> tuple[QuantumCircuit | None, QuantumCircuit | None, int]:
        """(output of one run, output at the fixed point, runs that lowered a figure)."""
        first = cur = self.once(src, snap)
        if cur is None:
            return None, None, 0
        runs = 1
        while runs < MAX_RUNS:
            nxt = self.once(cur)
            if nxt is None:
                break
            if not better(figures(nxt), figures(cur)):
                break
            cur, runs = nxt, runs + 1
        return first, cur, runs


# --------------------------------------------------------------------------- inputs

def load_file(path: str) -> QuantumCircuit:
    qc = qasm2.load(path, custom_instructions=LEGACY)
    qc.remove_final_measurements(inplace=True)
    return qc


def inputs(suites: list[str]):
    """(suite, name, source for catq-compile, Qiskit circuit) per circuit."""
    if "qsynth" in suites:
        for p in sorted(glob.glob(os.path.join(ROOT, "bench", "qasm", "qsynth", "*.qasm"))):
            yield "qsynth", os.path.basename(p)[:-5], p, load_file(p)
    if "nam" in suites:
        d = next((d for d in NAM_DIRS if os.path.isdir(d)), None)
        for p in sorted(glob.glob(os.path.join(d, "*.qasm"))) if d else []:
            yield "nam", os.path.basename(p)[:-5], p, load_file(p)
    if "qasmbench" in suites:
        for p in sorted(glob.glob(os.path.join(ROOT, "bench", "qasm", "qasmbench", "small",
                                               "*.qasm"))):
            yield "qasmbench", os.path.basename(p)[:-5], p, load_file(p)
    if "qrisp" in suites:
        sys.path.insert(0, HERE)
        sys.dont_write_bytecode = True
        from qrisp_compare import PROGRAMS
        from catq.qrisp_adapter import to_qiskit
        for name, f in PROGRAMS.items():
            obj, kw = f()
            qc = to_qiskit(obj, kw)
            yield "qrisp", name, qc, qc


# --------------------------------------------------------------------------- Qiskit passes

def _flat(stage):
    out = []
    for x in getattr(stage, "_tasks", []):
        for y in (x if isinstance(x, list) else [x]):
            out.append(y)
            out += _flat_tasks(y)
    return out


def _flat_tasks(y):
    out = []
    for z in getattr(y, "tasks", ()):
        out.append(z)
        out += _flat_tasks(z)
    return out


def pass_managers():
    """name -> a PassManager-like object with `run`, each followed by the translation stage."""
    pm = generate_preset_pass_manager(3, basis_gates=BASIS, seed_transpiler=0)
    trans = pm.translation
    init = {type(p).__name__: p for p in _flat(pm.init)}
    loop = {type(p).__name__: p for p in _flat(pm.optimization)}
    skip = {"Size", "Depth", "MinimumPoint", "GatesInBasis", "DoWhileController",
            "ConditionalController", "FlowControllerLinear", "UnitarySynthesis",
            "HighLevelSynthesis", "BasisTranslator", "ElidePermutations", "Split2QUnitaries"}
    out = {}
    for stage, table in (("init", init), ("opt", loop)):
        for name, p in table.items():
            if name in skip:
                continue
            tasks = [p, init["Split2QUnitaries"]] if name == "ConsolidateBlocks" else [p]
            out[f"{stage}:{name}"] = (PassManager(tasks), trans)
    init_ne = PassManager()
    for group in pm.init._tasks:
        tasks = [t for t in group if not isinstance(t, ElidePermutations)]
        if tasks:
            init_ne.append(tasks)
    out["stage:init (no elide)"] = (init_ne, trans)
    out["stage:optimization"] = (pm.optimization, trans)
    full = generate_preset_pass_manager(3, basis_gates=BASIS, seed_transpiler=0)
    full.init = init_ne
    out["preset (no elide)"] = (full, None)
    return out, full


def run_pm(pair, qc: QuantumCircuit) -> QuantumCircuit:
    a, b = pair
    out = a.run(qc)
    return b.run(out) if b is not None else out


# --------------------------------------------------------------------------- main

def fmt(fig, base):
    return [*fig, *(x - y for x, y in zip(fig, base))]


def main(args: list[str]) -> None:
    import qiskit

    snapped = args[:1] == ["--snap"]
    if snapped:
        args = args[1:]
    suites = args or ["qsynth", "nam", "qasmbench", "qrisp"]
    os.makedirs(OUT_DIR, exist_ok=True)
    pms, full = pass_managers()
    elide = PassManager([ElidePermutations()])
    stamp = (f"# qiskit {qiskit.__version__}, catq-compile level 2r unchecked at its fixed "
             f"point; {time.strftime('%Y-%m-%d %H:%M %Z')}\n")
    hb = ["suite", "circuit", "qubits", "cx_in", "cx_1", "gates_1", "runs", "cx", "depth2",
          "gates", "check"]
    hp = ["suite", "circuit", "pass", "cx", "depth2", "gates", "d_cx", "d_depth2", "d_gates",
          "check"]
    hr = ["suite", "circuit", "qiskit_cx", "qiskit_depth2", "qiskit_gates", "catq_cx",
          "catq_depth2", "catq_gates", "d_cx", "d_depth2", "d_gates", "runs", "check"]
    prefix = ("snap-" if snapped else "") + ("-".join(args) + "-" if args else "")
    if snapped:
        stamp = stamp.replace("at its fixed point", "at its fixed point after snapping")
    fb, fp, fr = (open(os.path.join(OUT_DIR, prefix + n), "w") for n in
                  ("base.tsv", "passes.tsv", "reverse.tsv"))
    for f, h in ((fb, hb), (fp, hp), (fr, hr)):
        f.write(stamp + "\t".join(h) + "\n")
    with tempfile.TemporaryDirectory(prefix="qiskit-passes-") as wd:
        cq = Catq(wd)
        for suite, name, src, qin in inputs(suites):
            first, base, runs = cq.fixpoint(src)
            if base is None:
                fb.write(f"{suite}\t{name}\t{qin.num_qubits}\trefused\n")
                continue
            if snapped:  # the base: snap, then catq-compile to its fixed point
                _, sb, sruns = cq.fixpoint(bare(base), snap=True)
                if sb is not None and better(figures(sb), figures(base)):
                    base, runs = sb, runs + sruns
            bfig = figures(base)
            chk = same_up_to_phase(qin, base)
            r = [suite, name, qin.num_qubits, figures(qin)[0], figures(first)[0],
                 figures(first)[2], runs, *bfig, chk]
            fb.write("\t".join(map(str, r)) + "\n")
            fb.flush()
            print("\t".join(map(str, r)), flush=True)
            bimg = None
            for pname, pair in pms.items():
                out = bare(run_pm(pair, base))
                fig = figures(out)
                if fig == bfig and out == base:
                    c = "same"
                else:
                    if bimg is None:
                        bimg = _image(base)
                    c = "nosim" if bimg is None else same_up_to_phase(bimg, out)
                fp.write("\t".join(map(str, [suite, name, pname, *fmt(fig, bfig), c])) + "\n")
                # a pass that lowers CX or gates, then catq-compile to its fixed point
                if c != "same" and (fig[0] < bfig[0] or fig[2] < bfig[2]):
                    _, pb, _ = cq.fixpoint(out, snap=True)
                    if pb is not None and not better(figures(pb), fig):
                        pb = out  # catq-compile's first run did not improve on the pass
                    if pb is not None:
                        c2 = "nosim" if bimg is None else same_up_to_phase(bimg, pb)
                        fp.write("\t".join(map(str, [suite, name, pname + " +catq",
                                                     *fmt(figures(pb), bfig), c2])) + "\n")
            # no pass: the base printed by qasm2.dumps (angles within 1e-12 of a rational
            # multiple of pi snapped to it), then catq-compile to its fixed point
            _, sb, _ = cq.fixpoint(bare(base), snap=True)
            if sb is not None and not better(figures(sb), bfig):
                sb = base  # no improvement: one more run of catq-compile can add gates
            if sb is not None:
                sfig = figures(sb)
                if sfig != bfig and bimg is None:
                    bimg = _image(base)
                c2 = "same" if sfig == bfig else (
                    "nosim" if bimg is None else same_up_to_phase(bimg, sb))
                fp.write("\t".join(map(str, [suite, name, "snap +catq", *fmt(sfig, bfig), c2]))
                         + "\n")
            # ElidePermutations: on the input, then catq-compile to its fixed point.
            if qin.count_ops().get("swap", 0) or qin.count_ops().get("permutation", 0):
                el = elide.run(qin)
                perm = el.layout.final_index_layout() if el.layout is not None else None
                esrc = bare(el)
                if isinstance(src, str):  # keep the exact angles of the file
                    esrc = os.path.join(wd, f"elided-{name}.qasm")
                    with open(esrc, "w") as f:
                        f.write(qasm2.dumps(bare(el)))
                _, eb, _ = cq.fixpoint(esrc)
                if eb is not None:
                    fig = figures(eb)
                    chk2 = eb.copy()
                    if perm is not None:
                        chk2.append(PermutationGate(perm), range(qin.num_qubits))
                    c = same_up_to_phase(qin, chk2)
                    fp.write("\t".join(map(str, [suite, name, "input:ElidePermutations",
                                                 *fmt(fig, bfig), c])) + "\n")
            fp.flush()
            # reverse: catq-compile on Qiskit's output
            qk = bare(full.run(qin))
            qfig = figures(qk)
            _, rb, rruns = cq.fixpoint(qk, snap=True)
            if rb is not None:
                rfig = figures(rb)
                c = same_up_to_phase(qk, rb) if rfig != qfig else "same"
                fr.write("\t".join(map(str, [suite, name, *qfig, *fmt(rfig, qfig), rruns, c]))
                         + "\n")
                fr.flush()
        cq.close()
    for f in (fb, fp, fr):
        f.close()


if __name__ == "__main__":
    main(sys.argv[1:])
