"""`compile_for_device`: catq-compile before and after routing a circuit onto a device.

The pipeline has three steps on one `catq-compile --serve` process:

  1. `VerifiedCompiler(permutation="layout")` with swap elision: the output permutation of the
     elided swaps is a relabelling of the final wires and costs no gate;
  2. Qiskit's Sabre layout and routing at optimization level 0 into {rx, ry, rz, cx, p}
     (`generate_preset_pass_manager(optimization_level=0, layout_method="sabre",
     routing_method="sabre")`, seeds `0..seeds-1`, the seed with fewest CX kept, ties broken by
     two-qubit depth); level 0 runs no optimization, so every two-qubit gate of the routed
     circuit lies on an edge of the map;
  3. the same compiler with `elide=False` on the routed circuit, whose wires are the physical
     qubits.

Without swap elision every stage of a run keeps the qubit pairs of the two-qubit statements
among those of its input, so a circuit routed on the map stays routed on it
(`QrunchConnect.routed_runCompile`); `compile_for_device` checks this on the output and raises
`OffMapGate` when a two-qubit gate is not on an edge. The coupling map is read as undirected,
as in the theorem: each edge is added in both directions.

The output carries one Qiskit `TranspileLayout`: the initial layout of the routing, and a final
layout that composes the routing's final permutation after the permutation of step 1, so that
`Operator.from_circuit(result.circuit)` is the input's operator up to the summed bound `eps`
(the global phase included, for a circuit without classical instructions and with as many
physical as virtual qubits).
"""
from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Iterable, Optional

from qiskit import QuantumCircuit
from qiskit.transpiler import CouplingMap, Layout, TranspileLayout, generate_preset_pass_manager

from .compiler import CompileReport, VerifiedCompiler, cx_count

BASIS = ["rx", "ry", "rz", "cx", "p"]


class OffMapGate(RuntimeError):
    """A two-qubit gate of the output is not on an edge of the coupling map."""


@dataclass
class RoutedResult:
    """`circuit`: the routed and compiled circuit on the physical qubits, with `layout`, its
    `TranspileLayout`; `eps`: the sum of the bounds of the two compiles (`None` when either is
    unchecked); `pre` and `post`: the reports of steps 1 and 3; `seed`: the routing seed kept;
    `cx_pre`, `cx_routed`, `cx_out`: CX after step 1, after routing and after step 3."""
    circuit: QuantumCircuit
    layout: TranspileLayout
    eps: Optional[float]
    pre: CompileReport
    post: CompileReport
    seed: int
    cx_pre: int
    cx_routed: int
    cx_out: int


def symmetric_map(coupling_map: CouplingMap | Iterable[Iterable[int]]) -> CouplingMap:
    """The coupling map with each edge in both directions."""
    edges = (coupling_map.get_edges() if isinstance(coupling_map, CouplingMap)
             else [tuple(e) for e in coupling_map])
    both = {(a, b) for a, b in edges} | {(b, a) for a, b in edges}
    return CouplingMap(sorted([a, b] for a, b in both))


def two_q_depth(qc: QuantumCircuit) -> int:
    return qc.depth(lambda ins: ins.operation.num_qubits == 2)


def off_map_gates(qc: QuantumCircuit, cmap: CouplingMap) -> list[tuple[str, tuple[int, ...]]]:
    """The multi-qubit gates of `qc` (barriers aside) whose qubits are not the two ends of an
    edge of `cmap`, as (name, qubits)."""
    edges = {tuple(e) for e in cmap.get_edges()}
    bad = []
    for ins in qc.data:
        if ins.operation.name == "barrier" or len(ins.qubits) < 2:
            continue
        qs = tuple(qc.find_bit(b).index for b in ins.qubits)
        if len(qs) != 2 or (qs not in edges and qs[::-1] not in edges):
            bad.append((ins.operation.name, qs))
    return bad


def bare(qc: QuantumCircuit) -> QuantumCircuit:
    """`qc` without its layout."""
    out = qc.copy()
    out._layout = None
    return out


def route(qc: QuantumCircuit, cmap: CouplingMap, seeds: int) -> tuple[QuantumCircuit, int]:
    """Sabre layout and routing at optimization level 0 into `BASIS`: the routed circuit with
    fewest CX over seeds `0..seeds-1` (ties: two-qubit depth) and its seed."""
    best = None
    for s in range(seeds):
        pm = generate_preset_pass_manager(optimization_level=0, coupling_map=cmap,
                                          basis_gates=BASIS, layout_method="sabre",
                                          routing_method="sabre", seed_transpiler=s)
        r = pm.run(qc)
        key = (cx_count(r), two_q_depth(r))
        if best is None or key < best[0]:
            best = (key, r, s)
    return best[1], best[2]


def compose_layout(routed: QuantumCircuit, out: QuantumCircuit,
                   sigma: list[int]) -> TranspileLayout:
    """The layout of `out`, a circuit on the wires of `routed`, when `routed` is the routing of
    a circuit that leaves the state of its source's qubit `q` on virtual wire `sigma[q]`. With
    `L` the initial layout (virtual to physical, ancillas included) and `F` the final layout of
    the routing (physical to physical), the state of qubit `q` ends on physical wire
    `F[L[sigma[q]]]`, and the new final layout maps physical `L[q]` to it."""
    lay = routed.layout
    m = routed.num_qubits
    if lay is None:
        init = list(range(m))
        lay = TranspileLayout(Layout({q: i for i, q in enumerate(routed.qubits)}),
                              {q: i for i, q in enumerate(routed.qubits)},
                              _input_qubit_count=m, _output_qubit_list=list(routed.qubits))
    else:
        init = lay.initial_index_layout(filter_ancillas=False)
    fin = (list(range(m)) if lay.final_layout is None
           else [lay.final_layout[q] for q in routed.qubits])
    inv = {p: v for v, p in enumerate(init)}
    s1 = list(sigma) + list(range(len(sigma), m))
    new = [fin[init[s1[inv[p]]]] for p in range(m)]
    return replace(lay, final_layout=Layout({out.qubits[p]: new[p] for p in range(m)}),
                   _output_qubit_list=list(out.qubits))


def compile_for_device(circuit: QuantumCircuit,
                       coupling_map: CouplingMap | Iterable[Iterable[int]], *,
                       seeds: int = 20, check: bool = True,
                       compiler: Optional[VerifiedCompiler] = None, **kw) -> RoutedResult:
    """catq-compile `circuit` (with swap elision), route it onto `coupling_map` (Sabre, level 0,
    fewest CX over `seeds` seeds) and catq-compile the routed circuit with `elide=False`.

    `check` and `kw` go to `VerifiedCompiler` (`level`, `snap`, `catq_compile`, ...);
    `compiler`, a `VerifiedCompiler(permutation="layout")`, reuses its server and its own
    settings instead (its `elide` is restored afterwards). Raises `ValueError` when `circuit` has a layout or more qubits than the map,
    `OffMapGate` when a two-qubit gate of the output is off the map, and `RuntimeError` when the
    second compile permutes the wires."""
    if circuit.layout is not None:
        raise ValueError("the input already has a layout")
    cmap = symmetric_map(coupling_map)
    if circuit.num_qubits > cmap.size():
        raise ValueError(f"{circuit.num_qubits} qubits on a map of {cmap.size()}")
    own = compiler is None
    vc = compiler if compiler is not None else VerifiedCompiler(
        check=check, permutation="layout", **kw)
    if vc.permutation != "layout":
        raise ValueError('the compiler must have permutation="layout"')
    elide = vc.elide
    try:
        vc.elide = True
        ours = vc.compile(circuit)
        pre = vc.last_report
        sigma = pre.final_permutation if pre.optimized else list(range(circuit.num_qubits))
        routed, seed = route(bare(ours), cmap, seeds)
        vc.elide = False
        out = vc.compile(bare(routed))
        post = vc.last_report
    finally:
        vc.elide = elide
        if own:
            vc.close()
    if post.optimized and post.final_permutation != list(range(out.num_qubits)):
        raise RuntimeError(f"the compile without elision permuted the wires: "
                           f"{post.final_permutation}")
    bad = off_map_gates(out, cmap)
    if bad:
        raise OffMapGate(f"{len(bad)} gates off the coupling map, first {bad[0]}")
    out = out.copy()
    out._layout = compose_layout(routed, out, sigma)
    eps = None if pre.eps is None or post.eps is None else pre.eps + post.eps
    return RoutedResult(circuit=out, layout=out.layout, eps=eps, pre=pre, post=post, seed=seed,
                        cx_pre=cx_count(ours), cx_routed=cx_count(routed), cx_out=cx_count(out))
