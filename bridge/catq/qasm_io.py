"""Printing a Qiskit circuit as the OpenQASM 2 that `catq-compile` reads.

Qubit `i` of the Qiskit circuit is `q[i]` in both files. Lean's `embedGate1` takes
`q[0]` as the most significant bit and Qiskit takes it as the least significant, so
the Lean unitary of a circuit is the Qiskit one conjugated by the bit reversal; the
same permutation acts on input and output, and equality of unitaries is preserved.

`lower` only prints: the meaning of each statement and the phase between its qelib1
matrix and the gates Lean imports are Lean's (`Qelib.listMatrix_lowerQ`), and
`catq-compile` prints its result in qelib1 itself (`QrunchBasis.printQelib`), which
`VerifiedCompiler` reads with Qiskit's `qasm2.loads`.
"""
from __future__ import annotations

import math
import re
from dataclasses import dataclass, field
from fractions import Fraction

from qiskit import QuantumCircuit
from qiskit.circuit import ControlFlowOp

PI = math.pi


class Unsupported(Exception):
    """An instruction the lowering does not translate; the caller returns the
    circuit unchanged and flags it."""


class AngleError(Exception):
    """An angle literal the decoder does not read."""


# --------------------------------------------------------------------------- angles

def encode_angle(theta: float) -> str:
    """The OpenQASM literal for `theta` radians that the importer reads: the
    shortest decimal `repr(float(theta))`, which the importer reads exactly as a
    rational number of radians (`OpenQASMParser.parseDecimal`).

    This is the one place where angles are encoded; the decimal differs from the
    double by less than half an ulp, and no theorem covers that step."""
    t = float(theta)
    return "0" if t == 0 else repr(t)


_ANGLE = re.compile(r"^(-?)(?:(\d+)\*)?pi(?:/(\d+))?$")
_DECIMAL = re.compile(r"^[+-]?(\d+(\.\d*)?|\.\d+)([eE][+-]?\d+)?$|^[+-]?\d+/\d+$")


def _pi_multiple(t: str) -> Fraction | None:
    if t == "0":
        return Fraction(0)
    m = _ANGLE.match(t)
    if not m:
        return None
    sign, k, d = m.groups()
    v = Fraction(int(k) if k else 1, int(d) if d else 1)
    return -v if sign else v


def decode_angle(text: str) -> Fraction:
    """The multiple of `pi` that an angle literal denotes. A `QasmAngle.toQASM`
    literal (`0`, `pi`, `-pi`, `k*pi` and each of the last three divided by `d`) is
    read exactly; a decimal `a` in radians, or a sum `a+B` of a decimal and such a
    literal, contributes `Fraction(a) / Fraction(math.pi)`, exact only up to the
    double `math.pi`."""
    t = text.replace(" ", "")
    v = _pi_multiple(t)
    if v is not None:
        return v
    if _DECIMAL.match(t):
        return Fraction(t) / Fraction(PI)
    head, plus, tail = t.rpartition("+")
    v = _pi_multiple(tail) if plus else None
    if v is not None and _DECIMAL.match(head):
        return Fraction(head) / Fraction(PI) + v
    raise AngleError(f"angle {text!r}")


def radians(q: Fraction) -> float:
    return float(q) * PI


# --------------------------------------------------------------------------- lowering

# name -> (number of angles, number of qubits): the qelib1 statements the Lean importer
# reads as `OpenQASMImport.QGate`. Their meaning, and the phase between the qelib1 matrix
# and the imported gates, are Lean's (`Qelib.listMatrix_lowerQ`); this table only checks
# arities before printing.
STATEMENTS: dict[str, tuple[int, int]] = {
    "h": (0, 1), "x": (0, 1), "y": (0, 1), "z": (0, 1), "s": (0, 1), "t": (0, 1),
    "tdg": (0, 1), "sdg": (0, 1), "sx": (0, 1), "sxdg": (0, 1),
    "rz": (1, 1), "rx": (1, 1), "ry": (1, 1), "p": (1, 1), "u1": (1, 1),
    "u2": (2, 1), "u": (3, 1), "u3": (3, 1),
    "cx": (0, 2), "cz": (0, 2), "swap": (0, 2), "cp": (1, 2), "cu1": (1, 2),
    "ccx": (0, 3), "ccz": (0, 3),
}

# skipped: the identity on the unitary
IDENTITY = {"id"}
# segment boundaries that act as the identity
ANNOTATION = {"barrier"}
# segment boundaries that are not unitary
NONUNITARY = {"measure", "reset"}


@dataclass
class Segment:
    """A maximal run of gates between boundary instructions."""
    ops: list = field(default_factory=list)


def is_classical(ins) -> bool:
    """A measurement, a reset, or an instruction with classical operands or control
    (`if_test` and the other control-flow operations, a gate with a condition)."""
    op = ins.operation
    return (op.name in NONUNITARY or isinstance(op, ControlFlowOp) or bool(ins.clbits)
            or getattr(op, "condition", None) is not None)


def _angles(op) -> list[float]:
    out = []
    for p in op.params:
        try:
            out.append(float(p))
        except TypeError as e:
            raise Unsupported(f"{op.name}: unbound parameter {p}") from e
    return out


def split_segments(circuit: QuantumCircuit) -> tuple[list[Segment], list, bool]:
    """The gate segments of `circuit`, the boundary instructions between them
    (`len(segments) == len(boundaries) + 1`), and whether the circuit is unitary.

    A boundary is a barrier or a classical instruction (`is_classical`: measurement,
    reset, classically controlled operation); each cuts every qubit, and the circuit is
    unitary when all its boundaries are barriers. Raises `Unsupported` on an unknown
    gate or an unbound parameter."""
    segs, notes, unitary = [Segment()], [], True
    for ins in circuit.data:
        op = ins.operation
        name = op.name
        classical = is_classical(ins)
        if name in ANNOTATION or classical:
            unitary = unitary and not classical
            notes.append(ins)
            segs.append(Segment())
            continue
        if name in IDENTITY:
            continue
        if name not in STATEMENTS:
            raise Unsupported(name)
        nang, nq = STATEMENTS[name]
        if len(op.params) != nang or len(ins.qubits) != nq:
            raise Unsupported(f"{name}: {len(op.params)} parameters on {len(ins.qubits)} qubits")
        qs = [circuit.find_bit(q).index for q in ins.qubits]
        segs[-1].ops.append((name, _angles(op), qs))
    return segs, notes, unitary


def lower(n: int, seg: Segment) -> str:
    """The OpenQASM 2 text of a segment on `n` qubits: each statement as Qiskit names it,
    its angles exact (`encode_angle`)."""
    lines = ["OPENQASM 2.0;", 'include "qelib1.inc";', f"qreg q[{n}];"]
    for name, angs, qs in seg.ops:
        args = f"({','.join(encode_angle(a) for a in angs)})" if angs else ""
        lines.append(f"{name}{args} {','.join(f'q[{i}]' for i in qs)};")
    return "\n".join(lines) + "\n"
