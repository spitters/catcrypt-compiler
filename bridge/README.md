# `bridge/` — the verified Lean compiler as a Qrunch compiler over Qiskit circuits

A uv project (Python 3.12, the version Kvantify Qrunch 1.4 requires; Qiskit 2.5.2, the newest
release that Qrisp 0.9 accepts). The compiler is the Lean executable `catq-compile`
(`CatCrypt/Quantum/Benchmark/QrunchCompile.lean`, `lake build catq-compile`); this directory
holds the Python side of Qrunch's `Compiler` protocol, an adapter for Qrisp, and their tests.
The comparisons with Qiskit are `bench/qrunch/compare.py` (OpenQASM 2 suites) and
`bench/qrunch/qrisp_compare.py` (Qrisp's algorithm library).

## The `catq` package

| Module | What it does |
|---|---|
| `catq/compiler.py` | `VerifiedCompiler(inner=None, level="2r", permutation="swaps")`: `compile(circuit)` runs `inner.compile` if given, splits the result at barriers and at classical instructions (measurement, reset, `if_test` and other classically controlled operations), which stay in place on their qubits and clbits, prints each segment as OpenQASM 2 (`qasm_io.lower`), sends it to one `catq-compile --serve` process kept for the life of the compiler (4 GB address-space cap), and reads the result with Qiskit's `qasm2.load`. A circuit without classical instructions gets the sum of the segments' phases in its global phase; in one with classical instructions each segment's phase multiplies the whole state and is unobservable, and is dropped. `last_report` carries the phase, the per-segment phases and the summed bound `eps` (`None` when unchecked; it includes the bound of angle snapping). The answer line of `catq-compile` is `ok <qubits> <cx_in> <cx_l2> <cx_out> <gates_out> <us> <us_import> <us_rounds> <us_kak> <us_zyz> <us_print> <phase> <eps> <rounds> <perm>`, read by index (`PHASE_FIELD`, `EPS_FIELD`, `ROUNDS_FIELD`, `PERM_FIELD`); `<perm>` is the output permutation `π 0,π 1,…` of swap elision: the state of input qubit `q` at the end of the segment is on output wire `π q`. The compiler carries the permutation across segments: each later operation and boundary instruction is relabelled to the wire that carries its qubit, so final measurements absorb it (each reads the wire of its qubit); when a moved qubit is not ended by a measurement, the output ends with the swaps (three `cx` each) that put every state back on its input wire. With `permutation="layout"`, for Qiskit callers, no swap is appended: the output carries a Qiskit `TranspileLayout` whose `final_layout` maps `out.qubits[q]` to `π q` (`with_final_permutation`; composed after the input's layout when it has one), so that `Operator.from_circuit(out)` is the input's operator up to the reported phase and `eps`; Qrunch's `UniversalGateCircuit` carries no layout, and the default `"swaps"` serves that path. `last_report.final_permutation`, `layouts` (the permutation at each segment boundary) and `swaps_appended` record it. `elide=False` and `snap=False` (`--no-elide`, `--no-snap`) turn off swap elision and angle snapping. An unbound parameter or unknown gate returns the input unchanged, with the reason in `last_report`. |
| `catq/qasm_io.py` | `split_segments` (the statements Lean reads: h x y z s sdg t tdg sx sxdg rx ry rz p u1 u u2 u3 cx cz swap cp cu1 ccx ccz; `id` dropped; barriers and `is_classical` instructions split), `lower` (prints a segment with exact angles: `encode_angle`, radians to the exact `k*pi/d` of the double). |
| `catq/qrisp_adapter.py` | `compile_qrisp(obj, **compiler_kwargs)` for a Qrisp `QuantumSession` (compiled with `QuantumSession.compile(**compile_kwargs)`), `QuantumVariable` or `QuantumCircuit`: decomposes in Qrisp the operations outside the statements, converts with `to_qiskit`, replaces what remains (`rzz`, `gphase`) by its Qiskit definition (`unroll`), runs `VerifiedCompiler`, and converts back with `qrisp.QuantumCircuit.from_qiskit`; returns the Qrisp circuit, both Qiskit circuits and the report. The bodies of `if_test` pass through unchanged. |
| `catq/routing.py` | `compile_for_device(circuit, coupling_map, *, seeds=20, check=True, compiler=None, **kw)`: catq-compile with swap elision (`permutation="layout"`), Qiskit's Sabre layout and routing at optimization level 0 into {rx, ry, rz, cx, p} (seeds `0..seeds-1`, fewest CX kept, ties by two-qubit depth; the map read as undirected), then catq-compile of the routed circuit with `elide=False`, on one server. Returns a `RoutedResult`: the circuit on the physical qubits with one `TranspileLayout` (the routing's initial layout; a final layout that composes the routing's final permutation after the permutation of the first compile, so that `Operator.from_circuit` is the input's operator up to `eps`), the summed `eps` of the two compiles, both reports, the seed and the CX after each step. Without swap elision every stage of a run keeps the qubit pairs among its input's, so a routed circuit stays routed (`QrunchConnect.routed_runCompile`); the output is checked anyway, and a two-qubit gate off the map raises `OffMapGate`. |
| `tests/test_routing.py` | Two 6-qubit circuits, one whose first compile fits both maps and one that needs routing swaps, on a line and on a 2x3 grid: `Operator.from_circuit` of the output equals the input exactly, global phase included; no two-qubit gate is off the map; the output has at most the CX of the routed circuit before the second compile and of the input routed with no catq-compile. |
| `tests/test_compiler.py` | On the 12 circuits of `bench/qasm/qsynth/`, on one of them transpiled to Qrunch's gate set, and on a circuit with every statement the importer reads and a barrier: the output equals the input exactly, global phase included (up to 10 qubits: Qiskit `Operator`; 16 qubits: four random statevectors), at levels `2` and `2r`, the latter with and without the checker. On a circuit with a mid-circuit measurement, an `if_test` with an else branch and a reset: the boundaries are in place, each segment equals its input up to phase (`Operator`), and the distribution of the clbits is the input's (`tests/branching.py`, exact branching simulation). Swaps before final measurements are absorbed by them (same distribution, no swap appended); a unitary circuit with swaps gets the remaining permutation appended and equals its input exactly; with `permutation="layout"` the same circuit (one swap, and two forming a 3-cycle) gets no swap, its `final_layout` is the reported permutation and `Operator.from_circuit` equals the input exactly, and on an input that already has a layout (Qiskit's level 3) the two layouts compose; a swap before a mid-circuit measurement relabels the measurement and the later segments (same distribution). |
| `tests/test_qrisp.py` | Skipped without qrisp. Qrisp's QPE and QAOA MaxCut at fixed angles: equal to the Qiskit input with the reported phase; a program with the mid-circuit measurements of the `gidney` and `jones` logical ANDs (`compile_mcm=True`): per-segment `Operator` and the exact distribution. |

## What is proved

[`QRUNCH.md`](../QRUNCH.md) states the structure of `catq-compile` and its theorems. With
`VerifiedCompiler(check=True)` (`catq-compile --check`) the fits of level `2r` run behind the
verified residual checker, and the answer line carries the bound `eps`; without it `eps` is
`unchecked`. For a circuit with classical instructions the theorems hold per segment.

Lean's `embedGate1` takes `q[0]` as the high-order bit and Qiskit as the low-order one; the
same relabelling acts on input and output.

## Running

```
cd bridge
uv sync --extra qrisp                            # or `uv sync` without Qrisp
uv run pytest -q
uv run python -I ../bench/qrunch/compare.py      # writes bench/qrunch/results.tsv
uv run python -I ../bench/qrunch/qrisp_compare.py  # writes bench/qrunch/qrisp/results.tsv
uv run python -I ../bench/qrunch/qrisp_compare.py --out results-layout.tsv
```
