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
phase relating the two programs' qelib1 matrices and the bound `eps` of the level. For a
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
from dataclasses import dataclass, field
from fractions import Fraction
from typing import Optional, Protocol

from qiskit import QuantumCircuit, qasm2

from .qasm_io import Unsupported, lower, split_segments

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
CATQ_COMPILE = os.environ.get("CATQ_COMPILE",
                              os.path.join(ROOT, ".lake", "build", "bin", "catq-compile"))
ADDRESS_CAP = 4000 * 1024 * 1024
LEVELS = ("1", "2", "2r")
PHASE_FIELD = 12
EPS_FIELD = 13
ROUNDS_FIELD = 14


class Compiler(Protocol):
    def compile(self, circuit: QuantumCircuit) -> QuantumCircuit: ...


class RunError(Exception):
    """`catq-compile` answered with an error or exited."""


@dataclass
class CompileReport:
    """`phase`: the radians added to the output's `global_phase` (the sum of
    `segment_phases` for a unitary circuit, else 0); `eps`: the sum of the segments'
    bounds, `None` when unchecked. For a unitary circuit, `M_in = e^{i phase} M_out` up to
    `eps` in the operator norm; for one with classical boundaries the same holds for each
    segment with its own phase."""
    optimized: bool
    reason: str = ""
    segments: int = 0
    unitary: bool = True
    phase: float = 0.0
    eps: Optional[float] = 0.0
    segment_phases: list[float] = field(default_factory=list)
    cx_in: int = 0
    cx_out: int = 0
    seconds: float = 0.0
    rows: list[str] = field(default_factory=list)


def cx_count(circuit: QuantumCircuit) -> int:
    return int(circuit.count_ops().get("cx", 0))


class _Server:
    """One `catq-compile --serve` process: a request line `<in> <out> <level>` per file,
    answered by `ok <qubits> <cx_in> <cx_l2> <cx_out> <gates_out> <us> ... <phase> <eps>
    <rounds>` (`PHASE_FIELD`, `EPS_FIELD` and `ROUNDS_FIELD` are their indices; phase and eps
    are summed over the rounds run) or `error <reason>`."""

    def __init__(self, exe: str, address_cap: int):
        self.proc = subprocess.Popen(["prlimit", f"--as={address_cap}", exe, "--serve"],
                                     stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                     text=True, bufsize=1, cwd=ROOT)

    def request(self, src: str, out: str, level: str, check: bool = False) -> str:
        if self.proc.poll() is not None:
            raise RunError(f"catq-compile exited with rc={self.proc.returncode}")
        flag = " --check" if check else ""
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
    every fit passes the checker, and the report's `eps` is `unchecked`."""

    def __init__(self, inner: Optional[Compiler] = None, level: int | str = "2r",
                 catq_compile: str = CATQ_COMPILE, address_cap: int = ADDRESS_CAP,
                 check: bool = False):
        level = str(level)
        if level not in LEVELS:
            raise ValueError("level must be 1, 2 or 2r")
        self.inner = inner
        self.level = level
        self.check = check
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
        row = self._server.request(src, out, self.level, self.check)
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
        try:
            with tempfile.TemporaryDirectory(prefix="catq-") as wd:
                for i, seg in enumerate(segs):
                    if i > 0:
                        out.append(notes[i - 1])
                    if not seg.ops:
                        continue
                    lean_out, row = self._run(lower(n, seg), wd, i)
                    rep.rows.append(row)
                    out.compose(lean_out, qubits=list(range(n)), inplace=True)
                    # M_in = e^{i phase} M_out for the qelib1 matrices (up to eps).
                    fields = row.split()
                    rep.segment_phases.append(float(Fraction(fields[PHASE_FIELD])))
                    phase += rep.segment_phases[-1]
                    eps = None if eps is None or fields[EPS_FIELD] == "unchecked" \
                        else eps + float(fields[EPS_FIELD])
        except (RunError, qasm2.QASM2ParseError) as e:
            rep.reason = f"{type(e).__name__}: {e}"
            rep.cx_out = rep.cx_in
            rep.seconds = time.perf_counter() - t0
            return circuit
        # A segment's phase multiplies the whole state; where a classical boundary follows,
        # it is unobservable and is dropped, and only a unitary circuit carries their sum.
        rep.phase = phase if unitary else 0.0
        rep.eps = eps
        out.global_phase = float(circuit.global_phase) + rep.phase
        rep.optimized = True
        rep.cx_out = cx_count(out)
        rep.seconds = time.perf_counter() - t0
        return out
