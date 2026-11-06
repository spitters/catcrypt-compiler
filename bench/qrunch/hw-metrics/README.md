# Hardware figures of catq-compile against Qiskit level 3

`../hw_metrics.py` measures three figures of the outputs of catq-compile and of Qiskit
`transpile(optimization_level=3)`, both into the basis {rx, ry, rz, cx, p} as in `../compare.py`:
CX count and two-qubit depth after routing onto three device coupling maps, the expected success
probability (ESP) of the routed circuit from published device calibrations, and the fault-tolerant
cost of the unrouted output (non-Clifford rotations, T gates, estimated T-count and T-depth after
Clifford+T synthesis). It also compiles the routed input with catq-compile (`rto`), checks that
every two-qubit gate of the result lies on a coupler of the device, and records wall-clock and CPU
time of both compilers.

## Commands and versions

```
cd bridge
.venv/bin/python -I ../bench/qrunch/hw_metrics.py import-calib DIR   # calib/*.json from the sources below
env OMP_NUM_THREADS=2 OPENBLAS_NUM_THREADS=2 RAYON_NUM_THREADS=2 \
  uv run --no-sync --project . python -I ../bench/qrunch/hw_metrics.py SUITE   # qsynth: 4 min, others under 1 min
.venv/bin/python -I ../bench/qrunch/hw_metrics.py summary                       # the tables below
```

SUITE is `qsynth`, `qasmbench`, `catcrypt` or `qrisp`; each run starts one `catq-compile --serve`
process and is run alone, one suite at a time.

Qiskit 2.5.2, Qrisp 0.9.10, NumPy 2.4.6, psutil 7.2.2, Python 3.12.3 (the bridge's uv environment,
no package added); the `catq-compile` binary of 2026-11-06 20:42. Run on 2026-11-06 with
RAYON_NUM_THREADS=2 (recorded in each TSV's header line).

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
| `rto` | routed table only: the routed `in` circuit of (1) (same Sabre run, fewest-CX seed) compiled by the same `VerifiedCompiler` server with swap elision off (`elide=False`, `--no-elide`), so that the output stays on the physical wires of the routed circuit |
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

## (3) Route, then catq-compile

`rto` compiles the routed `in` circuit of (1) on all device qubits, with the layout dropped, by the
same server and level as `ours` (`2r`, `--check`) but with swap elision off: an elided swap would
move a qubit's state to another wire and break the placement. The row's `rto_status` is `ok` when
the compile is accepted and its output permutation is the identity, `permuted` when the
permutation is not the identity, and the refusal reason otherwise; `rto_eps` is the reported bound
of the checked compile. `rto_viol` counts the multi-qubit gates of the output, before and after
translation into the basis, whose qubits are not the two ends of one coupler (a gate on three or
more qubits counts as one). The figures of (1) and (2) are then taken on `rto` as on the other
variants. Each variant also records `*_gates`, its gate count in the basis without barriers and
measurements.

## (4) Compile times

`*_wall` is wall-clock seconds and `*_cpu` user plus system CPU seconds of one compile:
`ours_*` and `qk_*` in `SUITE-ft.tsv` for the unrouted compiles, `rto_*` and `qkr_*` in
`SUITE-routed.tsv` (`qkr` covers its 20 seeded transpiles). The CPU of catq-compile is that of the
`catq-compile --serve` process (psutil, read before and after the call) plus the bridge's own
Python CPU during the call; the wall time includes the bridge's QASM writing and reading, and the
first compile of a suite includes the server's start-up (about 0.25 s). The CPU of Qiskit is
`time.process_time` of the benchmark process, which counts its Rayon threads (capped at
RAYON_NUM_THREADS=2).

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

The second table adds `rto`. Its ESP column is the median over the suite's circuits of
log10(ESP_v / ESP_in) for each variant v; the next column counts circuits where `rto` has the
higher, equal and lower ESP than `qkr`.

| suite | device | n | routed CX in / ours / qk / rto / qkr | depth2 rto / qkr | median log10(ESP / ESP in) ours / qk / rto / qkr | ESP rto vs qkr better-equal-worse | rto violations | rto refused |
|---|---|---|---|---|---|---|---|---|
| qsynth | garnet | 12 | 15643 / 15414 / 15456 / 14393 / 13983 | 9386 / 8996 | -0.424 / -0.431 / +2.830 / +2.712 | 5-0-7 | 0 | 0 |
| qsynth | aphrodite | 12 | 15679 / 15435 / 15414 / 14419 / 14041 | 9334 / 9116 | -1.112 / +0.839 / +7.182 / +6.007 | 4-0-8 | 0 | 0 |
| qsynth | kolkata | 12 | 21586 / 21372 / 21312 / 19488 / 19030 | 11626 / 11056 | -0.646 / -0.645 / +3.754 / +3.186 | 5-0-7 | 0 | 0 |
| qasmbench | garnet | 12 | 77 / 77 / 77 / 75 / 67 | 60 / 61 | +0.000 / +0.000 / +0.000 / +0.002 | 4-1-7 | 0 | 0 |
| qasmbench | aphrodite | 12 | 77 / 77 / 77 / 77 / 67 | 65 / 61 | +0.000 / +0.000 / +0.000 / +0.003 | 1-0-11 | 0 | 0 |
| qasmbench | kolkata | 12 | 86 / 86 / 86 / 80 / 76 | 71 / 67 | +0.000 / +0.000 / +0.000 / +0.003 | 5-1-6 | 0 | 0 |
| catcrypt | garnet | 5 | 162 / 153 / 153 / 147 / 143 | 133 / 137 | +0.000 / +0.000 / +0.000 / -0.004 | 5-0-0 | 0 | 0 |
| catcrypt | aphrodite | 5 | 162 / 153 / 153 / 147 / 143 | 133 / 134 | +0.000 / +0.000 / +0.000 / +0.044 | 3-0-2 | 0 | 0 |
| catcrypt | kolkata | 5 | 174 / 165 / 165 / 159 / 157 | 141 / 142 | +0.000 / +0.000 / +0.014 / +0.062 | 2-0-3 | 0 | 0 |
| qrisp | garnet | 7 | 4864 / 3642 / 3612 / 4070 / 3687 | 2859 / 2593 | +0.045 / +0.045 / +0.255 / +0.239 | 3-0-4 | 0 | 0 |
| qrisp | aphrodite | 7 | 4852 / 3618 / 3561 / 4019 / 3771 | 2804 / 2536 | +0.180 / +0.180 / +0.644 / +1.218 | 1-0-6 | 0 | 0 |
| qrisp | kolkata | 7 | 6169 / 4746 / 4689 / 4900 / 4427 | 3220 / 2701 | +0.031 / +0.040 / +0.213 / +0.028 | 4-0-3 | 0 | 0 |

Compile times summed over the suite (unrouted: one compile per circuit; routed: one per circuit
and device).

| suite | unrouted: ours wall / CPU s | qk wall / CPU s | routed, 3 devices: rto wall / CPU s | qkr (20 seeds) wall / CPU s |
|---|---|---|---|---|
| qsynth | 2.2 / 2.0 | 0.2 / 0.3 | 19.8 / 19.8 | 52.5 / 89.7 |
| qasmbench | 0.3 / 0.2 | 0.1 / 0.1 | 0.4 / 0.4 | 9.7 / 10.4 |
| catcrypt | 0.5 / 0.3 | 0.2 / 0.2 | 0.4 / 0.4 | 5.1 / 5.7 |
| qrisp | 3.6 / 3.4 | 0.3 / 0.5 | 16.4 / 16.3 | 34.3 / 55.0 |

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

Compiling after routing, catq-compile keeps every two-qubit gate on a coupler: the violation count
is 0 on all 108 routed rows, and every compile was accepted with the identity permutation. On
Q-Synth `rto` has 8.0% (Garnet, Aphrodite) and 9.7% (Kolkata) fewer routed CX than the routed
input, against 10.4 to 11.8% for `qkr`; it closes 71% (Garnet), 73% (Aphrodite) and 80% (Kolkata)
of the CX gap between `ours` routed and `qkr`, and remains 2.4 to 2.9% above `qkr`. Its median ESP
gain over the routed input is above `qkr`'s on all three devices, while per circuit `qkr` has the
higher ESP on 7 or 8 of the 12. On QASMBench and catcrypt `rto` has at most the routed CX of `ours`
and 2 to 10 more than `qkr` per suite and device. On the Qrisp programs `rto` is behind `ours` routed on the IQM maps
(4070 against 3642 on Garnet): on `shor15` the optimization before routing removes more CX (3859 to
2699 on Garnet) than the one after it (3859 routed to 3195). catq-compile runs single-threaded
(CPU equal to wall time); Qiskit's CPU is 1.6 to 1.7 times its wall time at two Rayon threads.
One `rto` compile of a routed Q-Synth circuit takes 0.14 to 1.36 s, about 7.5 times the 0.073 s
mean of one Qiskit level-3 transpile with the map (`qkr`, 20 per row).
