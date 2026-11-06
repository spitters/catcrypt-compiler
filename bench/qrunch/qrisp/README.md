# Qrisp's algorithm library through catq-compile

Programs of Qrisp 0.9.10 at fixed parameters, compiled by `QuantumSession.compile`, converted
to Qiskit (`bridge/catq/qrisp_adapter.py`, `to_qiskit`), and compiled by catq-compile at level
`2r` and by Qiskit 2.5.2 `transpile(optimization_level=3)`, both into {rx, ry, rz, cx, p}; best
of five runs in one process, interleaved. The times were taken on a shared machine with a Lean
build running (load average 3.5, recorded in the first line of each file).

```
cd bridge
uv sync --extra qrisp
uv run python -I ../bench/qrunch/qrisp_compare.py                                  # results.tsv
uv run python -I ../bench/qrunch/qrisp_compare.py --check --out results-check.tsv  # with the checker
```

The script's docstring defines the columns. `results.tsv` (unchecked fits):

| Program | Qubits | CX in | CX ours / Qiskit | 2q depth ours / Qiskit | Gates ours / Qiskit | ms ours / Qiskit |
|---|---|---|---|---|---|---|
| QPE, precision 4, two-qubit unitary | 6 | 82 | 82 / 76 (82) | 77 / 74 | 192 / 178 | 5.2 / 6.1 |
| Shor order finding, 7 mod 15 | 13 | 1912 | 1760 / 1271 (1283) | 938 / 716 | 3467 / 2584 | 98.8 / 65.8 |
| the same with Gidney's adder, mid-circuit measurements | 153 | 3425 | 3415 / 3396 (3408) | 2831 / 2827 | 6735 / 6876 | 267 / 220 |
| QAOA MaxCut, 6 vertices, depth 3 | 6 | 48 | 46 / 46 | 20 / 20 | 104 / 111 | 4.0 / 5.3 |
| VQE, Heisenberg ring of 6, depth 2 | 6 | 75 | 42 / 42 | 14 / 14 | 149 / 237 | 5.5 / 5.7 |
| Grover, 5 qubits, one marked value | 5 | 240 | 240 / 240 | 161 / 161 | 550 / 533 | 11.2 / 8.6 |
| QFT, 8 qubits | 8 | 68 | 68 / 56 (68) | 29 / 26 | 123 / 111 | 5.0 / 5.7 |
| Dicke state D(6,3) | 7 | 90 | 87 / 87 | 79 / 79 | 219 / 234 | 6.2 / 7.0 |

"CX in" is the count after catq-compile's import lowers cp, cz, swap and ccx. Qiskit's level 3
removes SWAP gates by permuting its output qubits (`ElidePermutations`); ours keeps the qubits
in place. The figure in parentheses is Qiskit's CX count with that pass removed, and the rows
with one are those where Qiskit permuted the output.

Every output equals its input: on the unitary rows the largest entrywise deviation is
1.1·10⁻¹⁴ (Operator up to 10 qubits, four random statevectors for Shor), Qiskit's taken
through its output permutation. The
153-qubit row is not simulated; its segmentation at the measurements is tested in
`bridge/tests/test_qrisp.py` on a small program. With `--check` the summed bound `eps` is at
most 2.2·10⁻¹³ on every row (`results-check.tsv`), and the checker raises our time on the
larger rows (Shor 182 ms, VQE 71 ms).

On Shor's circuit one run of catq-compile is not at its fixed point: feeding the output back
gives 1588, 1456, 1364, 1320 and 1308 CX over five more runs, against Qiskit's 1283 without
permutation elision. The other rows are at their fixed point after one run (checked over
three runs). The `if_test`
bodies of the mid-circuit row pass through the bridge unchanged (a `cz` each); Qiskit
translates them into the basis.
