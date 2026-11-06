"""`VerifiedCompiler`: the Lean circuit optimizer behind Qrunch's `Compiler` protocol,
over Qiskit circuits.

`compile(circuit)` runs the inner compiler (if any), splits the result at barriers and at
classical instructions (measurement, reset, classically controlled operations), which stay in
place on their qubits and clbits, prints each segment as OpenQASM 2 (`qasm_io.lower`: statement names, exact angles, qubit indices),
and sends it to one `catq-compile --serve` process kept for the life of the compiler. Lean
reads the statements with their qelib1 meaning, optimizes at `level` (`1` and `2`:
`fullOptimize`; `2r`: the resynthesis level `ResynthLevel.resynthAt`, Level 2 then `kakEmit`
and `zyzEmit`, behind the verified checker with `check`), and prints the result in qelib1 over {rx, ry, rz, cx, p}
(`QrunchBasis.printQelib`); Qiskit's `qasm2.loads` reads it back. The answer line carries the
phase relating the two programs' qelib1 matrices, the bound `eps` of the level and the output
permutation of swap elision, which the compiler carries to the later segments, lets final
measurements absorb, and otherwise undoes by appended swaps or, with
`permutation="layout"`, records in the output's Qiskit layout. For a
circuit without classical instructions the result's `global_phase` adds the segments' phases;
otherwise the phases are unobservable and are dropped. A circuit with a gate the lowering does
not translate or an unbound parameter, or whose run fails, is returned unchanged, and the
reason is in `last_report`.
"""
from __future__ import annotations

import os
import subprocess
import tempfile
import time
from dataclasses import dataclass, field, replace
from fractions import Fraction
from typing import Optional, Protocol

from qiskit import QuantumCircuit, qasm2
from qiskit.transpiler import Layout, TranspileLayout

from .qasm_io import Segment, Unsupported, lower, split_segments

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
CATQ_COMPILE = os.environ.get("CATQ_COMPILE",
                              os.path.join(ROOT, ".lake", "build", "bin", "catq-compile"))
ADDRESS_CAP = 4000 * 1024 * 1024
LEVELS = ("1", "2", "2r")
PERMUTATIONS = ("swaps", "layout")
PHASE_FIELD = 12
EPS_FIELD = 13
ROUNDS_FIELD = 14
PERM_FIELD = 15


class Compiler(Protocol):
    def compile(self, circuit: QuantumCircuit) -> QuantumCircuit: ...


class RunError(Exception):
    """`catq-compile` answered with an error or exited."""


@dataclass
class CompileReport:
    """`phase`: the radians added to the output's `global_phase` (the sum of
    `segment_phases` for a unitary circuit, else 0); `eps`: the sum of the segments'
    bounds (the snap bounds included), `None` when unchecked. For a unitary circuit,
    `M_in = e^{i phase} M_out` up to `eps` in the operator norm; for one with classical
    boundaries the same holds for each segment with its own phase, read through `layouts`.

    `final_permutation[q]` is the output wire that carries the state of input qubit `q` at
    the end of the compiled segments. `layouts[i]` is that permutation at the start of
    segment `i` and `layouts[-1]` at the end of the output circuit: `layouts[0]` is the
    identity, and `layouts[-1]` is the identity when `swaps_appended > 0`. Final
    measurements absorb the permutation (each reads the wire of its qubit); when a moved
    qubit is not ended by a measurement, the output ends with `swaps_appended` swaps (three
    `cx` each) that put every state back on its input wire. With `permutation="layout"` no
    swap is appended, and `final_permutation` is the `final_layout` of the output's layout
    (`with_final_permutation`)."""
    optimized: bool
    reason: str = ""
    segments: int = 0
    unitary: bool = True
    phase: float = 0.0
    eps: Optional[float] = 0.0
    segment_phases: list[float] = field(default_factory=list)
    final_permutation: list[int] = field(default_factory=list)
    layouts: list[list[int]] = field(default_factory=list)
    swaps_appended: int = 0
    cx_in: int = 0
    cx_out: int = 0
    seconds: float = 0.0
    rows: list[str] = field(default_factory=list)


def cx_count(circuit: QuantumCircuit) -> int:
    return int(circuit.count_ops().get("cx", 0))


def parse_perm(text: str) -> list[int]:
    """The permutation field of an answer line, `π 0,π 1,…` (`-` on no qubits)."""
    return [] if text == "-" else [int(w) for w in text.split(",")]


def swap_network(sigma: list[int]) -> list[tuple[int, int]]:
    """Swaps that move the state on wire `sigma[q]` to wire `q`, for every `q`; in reverse
    order they move the state on wire `q` to wire `sigma[q]`."""
    cur = list(sigma)
    pairs = []
    for q in range(len(cur)):
        w = cur[q]
        if w != q:
            p = cur.index(q)
            pairs.append((q, w))
            cur[q], cur[p] = q, w
    return pairs


def append_swaps(qc: QuantumCircuit, pairs: list[tuple[int, int]]) -> None:
    """Append each swap of `pairs` to `qc` as three `cx`."""
    for a, b in pairs:
        qc.cx(a, b); qc.cx(b, a); qc.cx(a, b)


def with_final_permutation(qc: QuantumCircuit, sigma: list[int],
                           base: Optional[TranspileLayout] = None) -> TranspileLayout:
    """The layout of a circuit `qc` that ends with the state its source leaves on wire `q` on
    wire `sigma[q]`, composed after `base`, the source's layout (`None`: the trivial layout).
    In Qiskit's convention `final_layout[qc.qubits[i]] = j` says that the state the circuit
    without that permutation leaves on wire `i` is on wire `j`; `Operator.from_circuit(qc)`
    applies the inverse permutation. A source `final_layout` `F` composes to `sigma[F[i]]`."""
    n = qc.num_qubits
    if base is None:
        trivial = {q: i for i, q in enumerate(qc.qubits)}
        return TranspileLayout(Layout(dict(trivial)), trivial,
                               final_layout=Layout({qc.qubits[i]: sigma[i] for i in range(n)}),
                               _input_qubit_count=n, _output_qubit_list=list(qc.qubits))
    # `Layout.to_permutation` reads the physical-to-virtual direction; this is the other one.
    f = (list(range(n)) if base.final_layout is None
         else [base.final_layout[q] for q in qc.qubits])
    return replace(base, final_layout=Layout({qc.qubits[i]: sigma[f[i]] for i in range(n)}))


def _measured_last(qc: QuantumCircuit) -> set[int]:
    """The wires whose last instruction other than a barrier is a measurement."""
    seen: set[int] = set()
    out: set[int] = set()
    for ins in reversed(qc.data):
        if ins.operation.name == "barrier":
            continue
        for q in ins.qubits:
            w = qc.find_bit(q).index
            if w not in seen:
                seen.add(w)
                if ins.operation.name == "measure":
                    out.add(w)
    return out


class _Server:
    """One `catq-compile --serve` process: a request line `<in> <out> <level>` per file,
    answered by `ok <qubits> <cx_in> <cx_l2> <cx_out> <gates_out> <us> ... <phase> <eps>
    <rounds> <perm>` (`PHASE_FIELD`, `EPS_FIELD`, `ROUNDS_FIELD` and `PERM_FIELD` are their
    indices; phase and eps are summed over the rounds run, eps includes the snap bound, and
    `perm` is the output permutation `π 0,π 1,…`: the state of input qubit `q` at the end is
    on output wire `π q`) or `error <reason>`."""

    def __init__(self, exe: str, address_cap: int):
        self.proc = subprocess.Popen(["prlimit", f"--as={address_cap}", exe, "--serve"],
                                     stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                     text=True, bufsize=1, cwd=ROOT)

    def request(self, src: str, out: str, level: str, check: bool = False,
                elide: bool = True, snap: bool = True) -> str:
        if self.proc.poll() is not None:
            raise RunError(f"catq-compile exited with rc={self.proc.returncode}")
        flag = (" --check" if check else "") + ("" if elide else " --no-elide") \
            + ("" if snap else " --no-snap")
        self.proc.stdin.write(f"{src} {out} {level}{flag}\n")
        self.proc.stdin.flush()
        return self.proc.stdout.readline().strip()

    def close(self) -> None:
        if self.proc.poll() is None:
            self.proc.stdin.close()
            self.proc.wait(timeout=10)


class VerifiedCompiler:
    """A `Compiler` whose optimization step is `FullOptimizer.fullOptimize` at `level` `1`
    or `2`, which preserves `unitaryDenote` (`runNamed_unitaryCorrect`), or at `2r` the
    resynthesis level `ResynthLevel.resynth` (Level 2, then `KAKPassSmall.kakEmit` and
    `ZYZPass.zyzEmit` behind the verified residual checker), whose output has at most as many
    CNOTs as Level 2 (`cnotCount_resynth_out_le`) and is within the reported `eps` of the
    input up to the reported phase, in the operator norm (`norm_listMatrix_resynth_sub_le`).
    The statements' meaning on both sides is qelib1's (`Qelib.listMatrix_lowerQ`,
    `QrunchBasis.qelibListMatrix_toQelib`). `level` is one of `LEVELS`; the integers 1 and 2
    name levels `1` and `2`. At `2r` the fits run behind the checker only with `check`
    (`catq-compile --check`); without it they are unchecked, replace the same blocks when
    every fit passes the checker, and the report's `eps` is `unchecked`.

    Before the rounds Lean elides `swap` statements into an output permutation
    (`SwapElide.elideQ`, off with `elide=False`) and snaps angles near multiples of `π/16`
    (`AngleSnap.snapQ`, off with `snap=False`; its bound is part of `eps`); the compile
    theorem is `QrunchRound.norm_runCompile_sub_le`. The permutation is carried across
    segments: every later operation and boundary instruction is relabelled to the wire that
    carries its qubit, so final measurements absorb it, and swaps (three `cx` each) are
    appended only when a moved qubit is not ended by a measurement (`CompileReport`).

    With `permutation="layout"` no swap is appended: the output carries a Qiskit
    `TranspileLayout` whose `final_layout` records the permutation, composed after the
    input's layout if it has one, so that `Operator.from_circuit(out)` is the input's
    operator (`Operator.from_circuit` of the input when it has a layout) up to the reported
    phase and `eps`. Qrunch's `UniversalGateCircuit` carries no layout, and the default
    `"swaps"` serves that path."""

    def __init__(self, inner: Optional[Compiler] = None, level: int | str = "2r",
                 catq_compile: str = CATQ_COMPILE, address_cap: int = ADDRESS_CAP,
                 check: bool = False, elide: bool = True, snap: bool = True,
                 permutation: str = "swaps"):
        level = str(level)
        if level not in LEVELS:
            raise ValueError("level must be 1, 2 or 2r")
        if permutation not in PERMUTATIONS:
            raise ValueError('permutation must be "swaps" or "layout"')
        self.permutation = permutation
        self.inner = inner
        self.level = level
        self.check = check
        self.elide = elide
        self.snap = snap
        self.catq_compile = catq_compile
        self.address_cap = address_cap
        self.last_report: Optional[CompileReport] = None
        self._server: Optional[_Server] = None

    def close(self) -> None:
        if self._server is not None:
            self._server.close()
            self._server = None

    def _run(self, text: str, workdir: str, idx: int) -> tuple[QuantumCircuit, str]:
        src = os.path.join(workdir, f"seg{idx}.qasm")
        out = os.path.join(workdir, f"seg{idx}.out.qasm")
        with open(src, "w") as f:
            f.write(text)
        if self._server is None:
            self._server = _Server(self.catq_compile, self.address_cap)
        row = self._server.request(src, out, self.level, self.check, self.elide, self.snap)
        if not row.startswith("ok") or not os.path.exists(out):
            raise RunError(row)
        return qasm2.load(out, custom_instructions=qasm2.LEGACY_CUSTOM_INSTRUCTIONS), row

    def compile(self, circuit: QuantumCircuit) -> QuantumCircuit:
        if self.inner is not None:
            circuit = self.inner.compile(circuit)
        t0 = time.perf_counter()
        rep = CompileReport(optimized=False, cx_in=cx_count(circuit))
        self.last_report = rep
        try:
            segs, notes, unitary = split_segments(circuit)
        except Unsupported as e:
            rep.reason = f"unsupported instruction: {e}"
            rep.cx_out = rep.cx_in
            return circuit
        rep.segments = len(segs)
        rep.unitary = unitary
        n = circuit.num_qubits
        out = circuit.copy_empty_like()
        phase = 0.0
        eps: Optional[float] = 0.0
        # sigma[q]: the output wire that carries the state of input qubit q.
        sigma = list(range(n))
        layouts = [list(sigma)]
        try:
            with tempfile.TemporaryDirectory(prefix="catq-") as wd:
                for i, seg in enumerate(segs):
                    if i > 0:
                        ins = notes[i - 1]
                        out.append(ins.replace(qubits=tuple(
                            out.qubits[sigma[circuit.find_bit(q).index]] for q in ins.qubits)))
                    if not seg.ops:
                        layouts.append(list(sigma))
                        continue
                    moved = Segment([(name, angs, [sigma[q] for q in qs])
                                     for name, angs, qs in seg.ops])
                    lean_out, row = self._run(lower(n, moved), wd, i)
                    rep.rows.append(row)
                    out.compose(lean_out, qubits=list(range(n)), inplace=True)
                    # M_in = W(pi) e^{i phase} M_out for the qelib1 matrices (up to eps).
                    fields = row.split()
                    rep.segment_phases.append(float(Fraction(fields[PHASE_FIELD])))
                    phase += rep.segment_phases[-1]
                    eps = None if eps is None or fields[EPS_FIELD] == "unchecked" \
                        else eps + float(fields[EPS_FIELD])
                    pi = parse_perm(fields[PERM_FIELD])
                    sigma = [pi[w] for w in sigma]
                    layouts.append(list(sigma))
        except (RunError, qasm2.QASM2ParseError) as e:
            rep.reason = f"{type(e).__name__}: {e}"
            rep.cx_out = rep.cx_in
            rep.seconds = time.perf_counter() - t0
            return circuit
        # A segment's phase multiplies the whole state; where a classical boundary follows,
        # it is unobservable and is dropped, and only a unitary circuit carries their sum.
        rep.phase = phase if unitary else 0.0
        rep.eps = eps
        rep.final_permutation = list(sigma)
        if self.permutation == "layout":
            if sigma != list(range(n)) or circuit.layout is not None:
                out._layout = with_final_permutation(out, sigma, circuit.layout)
        elif any(sigma[q] != q and sigma[q] not in _measured_last(out) for q in range(n)):
            pairs = swap_network(sigma)
            append_swaps(out, pairs)
            rep.swaps_appended = len(pairs)
            layouts[-1] = list(range(n))
        rep.layouts = layouts
        out.global_phase = float(circuit.global_phase) + rep.phase
        rep.optimized = True
        rep.cx_out = cx_count(out)
        rep.seconds = time.perf_counter() - t0
        return out
