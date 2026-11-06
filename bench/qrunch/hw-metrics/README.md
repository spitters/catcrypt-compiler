# Hardware figures of catq-compile against Qiskit level 3

`../hw_metrics.py` measures three figures of the outputs of catq-compile and of Qiskit
`transpile(optimization_level=3)`, both into the basis {rx, ry, rz, cx, p} as in `../compare.py`:
CX count and two-qubit depth after routing onto three device coupling maps, the expected success
probability (ESP) of the routed circuit from published device calibrations, and the fault-tolerant
cost of the unrouted output (non-Clifford rotations, T gates, estimated T-count and T-depth after
Clifford+T synthesis).

## Commands and versions

```
cd bridge
.venv/bin/python -I ../bench/qrunch/hw_metrics.py import-calib DIR   # calib/*.json from the sources below
RAYON_NUM_THREADS=4 .venv/bin/python -I ../bench/qrunch/hw_metrics.py qsynth      # 4 min
RAYON_NUM_THREADS=4 .venv/bin/python -I ../bench/qrunch/hw_metrics.py qasmbench
RAYON_NUM_THREADS=4 .venv/bin/python -I ../bench/qrunch/hw_metrics.py catcrypt
RAYON_NUM_THREADS=4 .venv/bin/python -I ../bench/qrunch/hw_metrics.py qrisp       # 45 s
.venv/bin/python -I ../bench/qrunch/hw_metrics.py summary                         # the tables below
```

Qiskit 2.5.2, Qrisp 0.9.10, NumPy 2.4.6, Python 3.12.3 (the bridge's uv environment, no package
added); catq-compile built from catcrypt-compiler `cc21c84c` (2026-11-06). Run on 2026-11-06.

Suites: `bench/qasm/qsynth/*.qasm` (12), `bench/qasm/qasmbench/small/*.qasm` (12, the files of
`../results-qasmbench.tsv`), `bench/qasm/catcrypt/*.qasm` (5) and the programs of
`../qrisp_compare.py` built the same way (7; `shor15_mcm` is left out: it has 153 qubits and
mid-circuit measurements, more qubits than any map).

Each suite writes `SUITE-routed.tsv` (one row per circuit and device) and `SUITE-ft.tsv` (one row
per circuit).

## Variants

| column prefix | circuit |
|---|---|
| `in` | the input, translated into the basis by Qiskit level 0 (no optimization) |
| `ours` | `VerifiedCompiler(level="2r", check=True, permutation="layout")`: resynthesis level behind the verified residual checker; the output permutation of swap elision is in the output's layout and no swap is appended |
| `qk` | `transpile(optimization_level=3, basis_gates=BASIS, seed_transpiler=0)` without a coupling map, as in `compare.py`; its `ElidePermutations` pass records swaps in the layout in the same way |
| `qkr` | routed table only: Qiskit level 3 given the coupling map (its own layout, routing and post-routing optimization), best of the same seeds |

The layouts of `ours` and `qk` are dropped before routing: the output permutation relabels final
wires and costs no gate. `ours_dev` is the deviation of `ours` from the input (`compare.deviation`,
through the layout); it is at most 1.5e-14 on every row.

## (1) Routed CX

`in`, `ours` and `qk` are each laid out and routed by the same pass manager,
`generate_preset_pass_manager(optimization_level=0, coupling_map=M, basis_gates=BASIS,
layout_method="sabre", routing_method="sabre", seed_transpiler=s)` for s = 0..19, and the seed with
the fewest CX (ties: two-qubit depth) is kept. Level 0 runs no optimization after routing; a SWAP
is three CX. Coupling maps are taken undirected (CX is available in both directions on every
Kolkata edge).

The router does not favour either side systematically. On the 36 Q-Synth rows the unrouted CX
counts of `ours` and `qk` are equal, and the routed difference `ours - qk` ranges from -33 to +45 CX
with both signs on each device; the summed difference is under 0.5%. With 5 seeds instead of 20 the
spread was -69 to +87, so the per-row differences on Q-Synth are router variance. The exception
is `shor15` (1271 unrouted CX on both sides), where `ours` routes to 30 to 57 more CX than `qk`
on every device at 5 and at 20 seeds: the two outputs order the same number of CX differently, and
Sabre routes Qiskit's order with 1.1 to 1.6% fewer SWAPs.

## (2) Expected success probability

Native-gate model. Each maximal run of one-qubit gates on a wire is one unitary U.

- IQM (Garnet, Aphrodite; native prx and cz, z rotations virtual): `cx(c,t)` is `h(t) cz(c,t) h(t)`,
  the Hadamards merged into the neighbouring runs; a run with |U00| = 1 is virtual, any other run
  is one prx.
- IBM (Kolkata; native rz virtual, sx, x, cx): |U00| = 1 virtual, |U00| = 0 one x, |U00| = 1/√2 one
  sx, otherwise two sx (the ZXZ form rz·sx·rz·sx·rz); `cx` is native.

Operations are scheduled as soon as their qubits are free; T is the end of the last one.

ESP = Π_g (1 − ε_g) · Π_{q active} exp(−t_q / T2_q)

- IBM: ε_g is the published `gate_error` (randomized benchmarking, which includes relaxation during
  the gate) and t_q = T − busy_q, the idle time of qubit q.
- IQM: ε_g = λ(d − 1)/d, the average gate infidelity of the published depolarizing parameter λ on
  d = 2^n levels (λ/2 for prx, 3λ/4 for cz). The IQM fake backends apply thermal relaxation
  separately during every gate, so t_q = T.

Readout is not counted: one measurement per active qubit on both sides. On Q-Synth and `shor15`
the ESP values lie between 1e-13 and 1e-286; there the ratio compares two circuits that no device
would run, and router variance moves it by several decades.

### Coupling maps and calibration sources

The `qiskit_ibm_runtime` package is not in the bridge environment. Its fake-backend data and the
IQM fake backends of `qiskit-on-iqm` were downloaded as source files (not executed; the IQM files are
read with `ast`) and converted by `import-calib` into `calib/*.json`, which record their source.

| device | map | qubits / couplers | 1q gate | 2q gate | median T1 / T2 | median 1q error | median 2q error |
|---|---|---|---|---|---|---|---|
| `garnet` | IQM Garnet, square lattice | 20 / 30 | prx 20 ns | cz 40 ns | 37.6 / 9.63 µs | λ 1.00e-3 (ε 5.0e-4) | λ 5.78e-3 (ε 4.3e-3) |
| `aphrodite` | IQM Aphrodite (Crystal 54), square lattice | 54 / 90 | prx 40 ns | cz 120 ns | 48.9 / 9.55 µs | λ 1.16e-3 (ε 5.8e-4) | λ 1.50e-2 (ε 1.1e-2) |
| `kolkata` | IBM Kolkata (Falcon r5.11), heavy hex | 27 / 28 | sx, x 35.6 ns | cx 380 ns (median) | 111.5 / 82.7 µs | sx 1.98e-4 | cx 7.54e-3 (max 6.28e-2 on 11–14) |

Per-qubit and per-coupler values are used, not the medians.

- Garnet: `IQMFakeGarnet` error profile `sample-chip`,
  https://github.com/iqm-finland/qiskit-on-iqm/blob/c41a1a9f5c77aa94e2569b359601dd733545c7b4/src/iqm/qiskit_iqm/fake_backends/fake_garnet.py
- Aphrodite: `IQMFakeAphrodite` error profile `sample-aphrodite-noise-model`,
  https://github.com/iqm-finland/qiskit-on-iqm/blob/bbd2e4816bd3b57ce15df73c1dc4d19dcd222c20/src/iqm/qiskit_iqm/fake_backends/fake_aphrodite.py
- Kolkata: `FakeKolkataV2` data, calibration of 2021-12-09,
  https://github.com/Qiskit/qiskit-ibm-runtime/tree/2a396172c25aa2971e99b434b430177745878a53/qiskit_ibm_runtime/fake_provider/backends/kolkata
  (`conf_kolkata.json`, `props_kolkata.json`)

## (5) Fault-tolerant cost

On the unrouted circuits in the basis, a rotation rx, ry, rz or p by θ is Clifford when θ is a
multiple of π/2, a T gate (T-count 1) at an odd multiple of π/4, and otherwise arbitrary, with a
tolerance of 1e-8 on θ/(π/4). An arbitrary rotation is synthesized to precision ε = 1e-10 by
Ross–Selinger at ⌈3·log2(1/ε)⌉ = 100 T gates, the O(1) term taken as 0. `rot_depth` is the depth
over non-Clifford rotations (a cx synchronises its two wires); `t_depth_est` is the same with weight
1 per T gate and 100 per arbitrary rotation. `t_count_est` = T gates + 100 · arbitrary rotations.

## Results

Routed CX and two-qubit depth are summed over the suite; the ESP column is the median over the
suite's circuits of log10(ESP_ours / ESP_qk), and the last column counts circuits where `ours` has
the higher, equal (within 0.001 decades) and lower ESP.

| suite | device | n | routed CX in / ours / qk / qkr | depth2 ours / qk | median log10(ESP ours / ESP qk) | ESP ours better-equal-worse |
|---|---|---|---|---|---|---|
| qsynth | garnet | 12 | 15643 / 15414 / 15456 / 13983 | 10195 / 10125 | +0.074 | 8-0-4 |
| qsynth | aphrodite | 12 | 15679 / 15435 / 15414 / 14041 | 10229 / 10032 | +1.004 | 9-0-3 |
| qsynth | kolkata | 12 | 21586 / 21372 / 21312 / 19030 | 12869 / 12915 | +0.005 | 6-0-6 |
| qasmbench | garnet | 12 | 77 / 77 / 77 / 67 | 63 / 63 | +0.000 | 0-12-0 |
| qasmbench | aphrodite | 12 | 77 / 77 / 77 / 67 | 65 / 65 | +0.000 | 0-12-0 |
| qasmbench | kolkata | 12 | 86 / 86 / 86 / 76 | 77 / 77 | +0.000 | 1-11-0 |
| catcrypt | garnet | 5 | 162 / 153 / 153 / 143 | 139 / 139 | +0.000 | 1-4-0 |
| catcrypt | aphrodite | 5 | 162 / 153 / 153 / 143 | 139 / 139 | +0.000 | 1-4-0 |
| catcrypt | kolkata | 5 | 174 / 165 / 165 / 157 | 147 / 147 | +0.001 | 1-4-0 |
| qrisp | garnet | 7 | 4864 / 3642 / 3612 / 3687 | 2599 / 2569 | +0.000 | 1-6-0 |
| qrisp | aphrodite | 7 | 4852 / 3618 / 3561 / 3771 | 2589 / 2597 | +0.000 | 1-5-1 |
| qrisp | kolkata | 7 | 6169 / 4746 / 4689 / 4427 | 3235 / 3203 | -0.008 | 1-2-4 |

| suite | n | non-Clifford rot. in / ours / qk | T gates in / ours / qk | est. T-count in / ours / qk | est. T-depth in / ours / qk |
|---|---|---|---|---|---|
| qsynth | 12 | 4428 / 4396 / 4756 | 0 / 4 / 311 | 442800 / 439204 / 444811 | 257700 / 257800 / 259411 |
| qasmbench | 12 | 42 / 39 / 48 | 33 / 31 / 33 | 933 / 831 / 1533 | 713 / 519 / 1115 |
| catcrypt | 5 | 121 / 92 / 106 | 58 / 48 / 51 | 6358 / 4448 / 5551 | 4238 / 4330 / 4834 |
| qrisp | 7 | 2083 / 1490 / 1628 | 656 / 466 / 516 | 143356 / 102866 / 111716 | 58175 / 46343 / 49168 |

Routed through the same router, the outputs of catq-compile and of Qiskit level 3 have the same CX
count to within router variance, except `shor15` (+1.1 to +1.6% for ours), and their ESP agrees
to within that variance. Qiskit level 3 given the coupling map (`qkr`) routes the input and then
optimizes, and reaches 9 to 11% fewer routed CX on Q-Synth and 5 to 13% fewer on the QASMBench
and catcrypt circuits; on the Qrisp circuits it is behind both on the IQM maps, where `shor15`
gains more from optimizing before routing. In the fault-tolerant count catq-compile has fewer
non-Clifford rotations than Qiskit on every suite (7.6% fewer on Q-Synth, 8 to 19% fewer on the
others). Qiskit's level 3 turns Clifford or T rotations into arbitrary ones on `grover_n2`,
`grover2`, `vqe_heisenberg`, `dicke` and 8 of the 12 Q-Synth rows, where its estimated T-count
rises above the input's. catq-compile
raises the estimated T-count above the input's on two circuits: `amp3_ccz` (28 T gates in; out 24 T
gates and 6 arbitrary rotations, 624) and `qaoa_maxcut` (42 to 44 arbitrary rotations); Qiskit
raises both further (824 and 50 rotations).
