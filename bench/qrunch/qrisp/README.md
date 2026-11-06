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

`results-layout.tsv` (`--out results-layout.tsv`, 2026-11-06, load average 4.5) adds the
`ours_lay_*` columns: `VerifiedCompiler(permutation="layout")` returns the output permutation
of swap elision in the output's `final_layout` instead of appending swaps, as Qiskit does. With
it ours has 76 CX on QPE, 56 on the QFT and 1271 on Shor, Qiskit's counts on all three, and
3403 against Qiskit's 3396 on the mid-circuit row; the deviation through
`Operator.from_circuit` is at most 8.2·10⁻¹⁵ on the unitary rows. The other columns of that
file were measured with a newer `catq-compile` than the table above (Shor 1283 CX without the
layout).

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

## Programs of Qrisp's tutorials

`--tutorials` runs the programs of the tutorials in Qrisp's documentation
(`documentation/source/general/tutorial/` of github.com/eclipse-qrisp/Qrisp), with the
notebooks' code, into `results-tutorials.tsv`:

```
uv run python -I ../bench/qrunch/qrisp_compare.py --tutorials --check
```

| Row | Program and size | Qrisp functions |
|---|---|---|
| `tsp` | TSP tutorial, 4 cities: Grover search over the three permutation specifiers (5 qubits), oracle `eval_distance_threshold` with the QPE route distance at precision 5 and threshold 0.4, one iteration (the tutorial's `winner_state_amount`), no final measurement | `demux`, `as_hamiltonian`, `QPE(iter_spec=True)`, `lifted`, `auto_uncompute`, `grovers_alg` |
| `backtrack_binary` | Sudoku tutorial, first part: binary tree of depth 3, `accept` marks the path [1,1,1], `reject` cuts [0] at height 2; phase estimation at precision 3 | `QuantumBacktrackingTree`, `init_node`, `estimate_phase` |
| `sudoku` | Sudoku tutorial, final part: the 4x4 board with three empty fields, tree depth 4 over 2-qubit branches, `subspace_optimization=True`, phase estimation at precision 3 | `QuantumBacktrackingTree`, `QuantumDictionary`, `mcx(method="balauca")`, `control` |
| `hhl` | HHL tutorial's system A = [[3/8, 1/8], [1/8, 3/8]], b = (1, 1) and its evolution `QubitOperator.from_matrix(A).to_pauli().trotterization()` (t = -π, one step), through the static `HHL` at precision 3; the eigenvalue inversion rotates the ancilla by 2 arcsin(1/k) on QPE value k/8 | `qrisp.algorithms.hhl.HHL`, `prepare`, `QPE` |
| `iqae_qmci` | QMCI tutorial: the state function of the integral of x² over [0, 1] (x in `QuantumFloat(3, -3)`, y in `QuantumFloat(6, -6)`) and one amplitude-amplification iteration, the circuit of `IQAE`'s round K = 3 | `auto_uncompute`, `amplitude_amplification` (the body of `IQAE`'s `quantum_step`) |
| `counting` | `quantum_counting` with its docstring's oracle (z on the last qubit) on 4 qubits, precision 4 | `quantum_counting`, `QPE`, `diffuser` |

The tutorial's own HHL is a repeat-until-success program in Jasp (`RUS`, mid-circuit
measurements), which the static path of the adapter does not take; the row uses the library's
static `HHL` on the tutorial's matrix and evolution instead. `IQAE` and `QMCI` run a sequence of
circuits whose iteration counts depend on measured frequencies; the row is one of them.

Each circuit is compiled once per compiler (after a warm-up of both), so the times are rough;
they were taken with load average 15 (other jobs on the box), and ours includes the checker.
2026-11-06, catq-compile level `2r --check`:

| Program | Qubits | CX in | CX ours / Qiskit | 2q depth ours / Qiskit | Gates ours / Qiskit | Deviation ours / Qiskit | ms ours / Qiskit |
|---|---|---|---|---|---|---|---|
| TSP, 4 cities, Grover with QPE oracle | 21 | 1804 | 1742 / 1742 (1754) | 1059 / 1059 | 3549 / 3690 | 4.3·10⁻¹⁷ / 7.8·10⁻¹⁷ | 1051 / 91 |
| Backtracking, binary tree of depth 3 | 16 | 989 | 975 / 972 (975) | 596 / 596 | 2076 / 2614 | 2.5·10⁻¹⁵ / 1.3·10⁻¹⁵ | 2066 / 32 |
| Backtracking, Sudoku with 3 empty fields | 24 | 3037 | 3037 / 3034 (3037) | 1227 / 1227 | 7166 / 7777 | 1.8·10⁻¹⁶ / 3.8·10⁻¹⁶ | 1603 / 95 |
| HHL, 2x2 system, precision 3 | 6 | 256 | 231 / 231 (237) | 163 / 163 | 516 / 538 | 3.3·10⁻¹⁵ / 6.7·10⁻¹⁵ | 61 / 8 |
| QMCI, one IQAE round (K = 3) | 25 | 2489 | 2347 / 2347 | 808 / 808 | 4832 / 4950 | not simulated | 2923 / 133 |
| Quantum counting, 4 qubits, precision 4 | 8 | 528 | 513 / 507 (513) | 439 / 436 | 1157 / 1260 | 1.2·10⁻¹⁴ / 1.0·10⁻¹⁴ | 227 / 19 |

The figure in parentheses is Qiskit's CX count without `ElidePermutations`, as above. With
`permutation="layout"` ours has Qiskit's CX count on every row (972 on the binary tree, 3034
on the Sudoku, 507 on counting). All six circuits are unitary. The deviation is the entrywise
maximum through `Operator` on the rows of at most 12 qubits (HHL, counting), over four random
statevectors (Qiskit's `Statevector.evolve`) on the 16-qubit row, and over two random
statevectors on the TSP (21 qubits) and Sudoku (24) rows. `Statevector.evolve` takes about
0.8 s per gate at 22 qubits, so above 20 qubits the script uses `_simulate`: numba kernels
that apply the circuit's gates, fused into blocks of at most three qubits, in place and one
state at a time (peak RSS 0.5 GiB at 21 qubits, 1.2 GiB at 24). On the 16-qubit row it agrees
with `Statevector.evolve` to 6·10⁻¹⁷, and appending `rz(10⁻³)` to the input gives a deviation
of 7·10⁻⁶ there. An entry of a random state has magnitude about 2^(-n/2), so the statevector
deviations are smaller than the Operator deviations of the small rows. The TSP and Sudoku rows
were rerun for this check (22:57 and 23:23), so their times come from that run, and Qiskit's
gate count on the Sudoku differs by 3 from the first run. The QMCI row (25 qubits, 0.5 GiB per
state) is not checked: its run was killed for low memory, and it needs MemAvailable above
3 GB. The checker's
summed bound `eps` is at most 2.3·10⁻¹² on every row. Qrisp built every program, and
catq-compile refused none.
