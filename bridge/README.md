# `bridge/` — the verified Lean compiler as a Qrunch compiler over Qiskit circuits

A uv project (Python 3.12, the version Kvantify Qrunch 1.4 requires; Qiskit 2.6.1). The
compiler is the Lean executable `catq-compile` (`CatCrypt/Quantum/Benchmark/QrunchCompile.lean`,
`lake build catq-compile`); this directory holds the Python side of Qrunch's `Compiler`
protocol and its tests. The comparison with Qiskit is `bench/qrunch/compare.py`.

## The `catq` package

| Module | What it does |
|---|---|
| `catq/compiler.py` | `VerifiedCompiler(inner=None, level="2r")`: `compile(circuit)` runs `inner.compile` if given, splits the result at barriers, prints each segment as OpenQASM 2 (`qasm_io.lower`), sends it to one `catq-compile --serve` process kept for the life of the compiler (4 GB address-space cap), reads the result with Qiskit's `qasm2.load`, and sets the global phase from the phase on the answer line. A measurement, reset, classical condition, unbound parameter or unknown gate returns the input unchanged, with the reason in `last_report`. |
| `catq/qasm_io.py` | `split_segments` (the statements Lean reads: h x y z s sdg t tdg sx sxdg rx ry rz p u1 u u2 u3 cx cz swap cp cu1 ccx ccz; `id` dropped; barriers split), `lower` (prints a segment with exact angles: `encode_angle`, radians to the exact `k*pi/d` of the double). |
| `tests/test_compiler.py` | On the 12 circuits of `bench/qasm/qsynth/`, on one of them transpiled to Qrunch's gate set, and on a circuit with every statement the importer reads and a barrier: the output equals the input exactly, global phase included (up to 10 qubits: Qiskit `Operator`; 16 qubits: four random statevectors), at levels `2` and `2r`, the latter with and without the checker. |

## What is proved

[`QRUNCH.md`](../QRUNCH.md) states the structure of `catq-compile` and its theorems. With
`VerifiedCompiler(check=True)` (`catq-compile --check`) the fits of level `2r` run behind the
verified residual checker, and the answer line carries the bound `eps`; without it `eps` is
`unchecked`.

Lean's `embedGate1` takes `q[0]` as the high-order bit and Qiskit as the low-order one; the
same relabelling acts on input and output.

## Running

```
cd bridge
uv sync
uv run python -P -m pytest tests -q
uv run python -I ../bench/qrunch/compare.py      # writes bench/qrunch/results.tsv
```
