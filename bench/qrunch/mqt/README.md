# MQT Bench through catq-compile

MQT Bench 2.3.0 (`mqt.bench`, the benchmark suite of the Munich Quantum Toolkit), every one of
its 36 algorithm families at the target-independent level (`BenchmarkLevel.INDEP`), compiled by
catq-compile at level `2r` behind the verified checker (`VerifiedCompiler(level="2r",
check=True)`) and by Qiskit 2.5.2 `transpile(optimization_level=3)`, both into
{rx, ry, rz, cx, p}. `bench/qrunch/mqt_compare.py` defines the columns in its docstring.

Inputs. MQT's target-independent level is the algorithm already transpiled by Qiskit at
level 2 (MQT's default, `seed_transpiler=10`), with its parameters bound by MQT to uniform
angles in [0, 2π) from `numpy.random.default_rng(10)`; `graphstate` uses `seed=10`. Its
circuits keep composite gates (`MAJ`, `qft_dg`, `Q`, `rzz`, `mcphase`, `c-unitary`, ...),
which the bridge does not read, so the script unrolls each by
`transpile(optimization_level=0)` into the statements `catq.qasm_io` lowers and removes the
final measurements; that circuit is the input of both compilers. The sizes are the valid
`circuit_size` nearest to 5, 8, 12 and 16 (ties to the smaller; for example 4 for families
that need an even size, 13 for the Steane code, 17 for Shor's nine-qubit code, 18 for
`shor`). `iqpe` has two qubits at every size (the size is its number of rounds).

Times are from one run per circuit, on a shared machine (load average per row in the last
column); the first row of each run includes the start of the `catq-compile` process. The
deviation is computed on the whole operator where it is cheap (`check` = op: up to 12
qubits), otherwise on four random statevectors (sv4) or one (sv1, `qwalk` 16 and `shor` 18),
and segment by segment up to a phase for the circuits with mid-circuit measurements (seg:
`dynamic_qft`, `ghz_dynamic`, `iqpe`, the two error-correction codes).

```
cd bridge
uv sync --extra mqt
OMP_NUM_THREADS=2 OPENBLAS_NUM_THREADS=2 RAYON_NUM_THREADS=2 \
  uv run python -I ../bench/qrunch/mqt_compare.py [--append] [--timeout 120] [FAMILY ...]
```

`results.tsv` (2026-11-06) was written in seven such runs, each a group of families (the first
without `--append`), with a per-compile timeout of 120 to 200 s; the last three ran under a
memory-admission wrapper with the thread counts above, after the first four, with numpy's and
Qiskit's thread pools unbounded, had loaded the shared machine to a stall.

## Summary per family

Sums over the sizes of the family. "CX in" is the input translated into the basis without
optimization. Gates exclude measurements, resets and barriers; an `if_else` counts as one.

| Family | Sizes | CX in | CX ours / Qiskit | 2q depth ours / Qiskit | Gates ours / Qiskit | ms ours / Qiskit |
|---|---|---|---|---|---|---|
| ae | 5 8 12 16 | 499 | 448 / 448 | 198 / 198 | 1089 / 1299 | 367 / 24 |
| bmw_quark_cardinality | 5 8 12 16 | 222 | 222 / 222 | 222 / 222 | 1088 / 1112 | 120 / 20 |
| bmw_quark_copula | 4 8 12 16 | 420 | 420 / 420 | 116 / 116 | 1044 / 1102 | 176 / 25 |
| bv | 5 8 12 16 | 17 | 17 / 17 | 17 / 17 | 63 / 100 | 106 / 21 |
| cdkm_ripple_carry_adder | 4 8 12 16 | 260 | 260 / 260 | 220 / 220 | 564 / 564 | 107 / 22 |
| dj | 5 8 12 16 | 37 | 37 / 37 | 37 / 37 | 117 / 157 | 29 / 18 |
| draper_qft_adder | 4 8 12 16 | 340 | 320 / 320 | 152 / 152 | 820 / 784 | 151 / 20 |
| dynamic_qft | 5 8 12 16 | 0 | 0 / 0 | 0 / 0 | 306 / 306 | 26 / 135 |
| full_adder | 4 8 12 16 | 259 | 253 / 253 | 214 / 214 | 553 / 553 | 37 / 63 |
| ghz | 5 8 12 16 | 37 | 37 / 37 | 37 / 37 | 45 / 45 | 96 / 23 |
| ghz_dynamic | 5 8 12 16 | 54 | 54 / 54 | 38 / 38 | 133 / 133 | 20 / 50 |
| graphstate | 5 8 12 16 | 41 | 41 / 41 | 19 / 19 | 123 / 191 | 11 / 19 |
| grover | 5 8 12 | 31556 | 31550 / 31550 | 26851 / 26851 | 74555 / 78207 | 34355 / 547 |
| half_adder | 5 7 11 15 | 333 | 299 / 299 | 173 / 173 | 675 / 703 | 304 / 52 |
| hhl | 5 8 12 16 | 862 | 785 / 785 | 360 / 360 | 1838 / 1852 | 642 / 40 |
| hrs_cumulative_multiplier | 5 9 13 17 | 3900 | 3540 / 3620 | 3381 / 3461 | 8720 / 9408 | 1146 / 103 |
| iqpe | 5 8 12 16 | 72 | 68 / 68 | 68 / 68 | 530 / 497 | 80 / 116 |
| modular_adder | 4 8 12 16 | 260 | 242 / 242 | 220 / 220 | 484 / 466 | 258 / 28 |
| multiplier | 4 8 12 16 | 2285 | 2139 / 2139 | 1983 / 1983 | 5143 / 5298 | 622 / 75 |
| qaoa | 5 8 12 16 | 452 | 452 / 452 | 166 / 166 | 962 / 1054 | 163 / 23 |
| qft | 5 8 12 16 | 448 | 448 / 446 | 140 / 140 | 978 / 971 | 132 / 28 |
| qftentangled | 5 8 12 16 | 485 | 485 / 483 | 148 / 148 | 1015 / 1016 | 152 / 25 |
| qnn | 5 8 12 16 | 37 | 37 / 37 | 37 / 37 | 205 / 205 | 27 / 23 |
| qpeexact | 5 8 12 16 | 446 | 442 / 442 | 192 / 192 | 1004 / 1033 | 212 / 25 |
| qpeinexact | 5 8 12 16 | 448 | 448 / 448 | 198 / 198 | 1015 / 1048 | 84 / 25 |
| qwalk | 5 8 12 16 | 21252 | 21204 / 21204 | 16989 / 16989 | 51053 / 54348 | 42649 / 647 |
| randomcircuit | 5 8 12 16 | 1680 | 1607 / 1607 | 644 / 644 | 3835 / 4125 | 2355 / 205 |
| rg_qft_multiplier | 4 8 12 16 | 1400 | 1190 / 1190 | 889 / 889 | 2600 / 2577 | 810 / 105 |
| seven_qubit_steane_code | 13 | 46 | 46 / 46 | 19 / 19 | 78 / 84 | 13 / 28 |
| shor | 18 | 10764 | 10512 / 10277 | 7172 / 7067 | 23077 / 33907 | 17671 / 1630 |
| shors_nine_qubit_code | 17 | 40 | 40 / 40 | 18 / 18 | 68 / 72 | 9 / 20 |
| vbe_ripple_carry_adder | 4 7 13 16 | 288 | 232 / 232 | 168 / 168 | 524 / 529 | 50 / 51 |
| vqe_real_amp | 5 8 12 16 | 111 | 111 / 111 | 53 / 53 | 275 / 275 | 336 / 40 |
| vqe_su2 | 5 8 12 16 | 111 | 111 / 111 | 53 / 53 | 439 / 545 | 64 / 46 |
| vqe_two_local | 5 8 12 16 | 672 | 672 / 672 | 152 / 152 | 836 / 836 | 84 / 69 |
| wstate | 5 8 12 16 | 74 | 74 / 74 | 45 / 45 | 152 / 202 | 39 / 40 |

On 128 of the 134 compiled circuits the CX counts are equal (MQT's inputs are already the
output of Qiskit's level 2). Ours has fewer CX on `hrs_cumulative_multiplier` at 9, 13 and 17 qubits
(476, 1062, 1880 against 484, 1086, 1928) and more on `qft` and `qftentangled` at 16 qubits
(240 and 255 against 238 and 253) and on `shor` 18 (10512 against 10277). On the two QFT rows
Qiskit's output deviates from the input by 3.3·10⁻⁷ and 3.4·10⁻⁷ and on `shor` by
7.5·10⁻⁸, where it drops small rotations (its default approximation degree); ours stays
within 1.4·10⁻¹³ on every row, and the `ours_lay_*` columns (output permutation in the
layout) have the same CX counts as the main columns. The summed gate counts of ours are at
most Qiskit's on 31 of the 36 families (more on `draper_qft_adder`, `iqpe`, `modular_adder`,
`qft` and `rg_qft_multiplier`). Qiskit is faster on 27 families, by a factor of about 60 on
`grover` and `qwalk`; ours is faster on `dynamic_qft`, `full_adder`, `ghz_dynamic`,
`graphstate`, `iqpe` and the two error-correction codes, and within 2 % on
`vbe_ripple_carry_adder` and `wstate`.

`grover` at 16 qubits did not finish within 150 s and has a row with that reason; `shor`,
`seven_qubit_steane_code` and `shors_nine_qubit_code` have rows "no instance" for the sizes
MQT Bench does not generate near the requested one. No circuit was refused for an
unsupported gate or an unbound parameter after the unrolling.
