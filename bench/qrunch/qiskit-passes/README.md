# Qiskit's level-3 passes on catq-compile's output

[`../qiskit_passes.py`](../qiskit_passes.py) compiles each circuit of the four suites (Q-Synth,
Nam, QASMBench small, the Qrisp programs of `qrisp_compare.py`; 62 circuits) with catq-compile
at level 2r, feeding the output back until neither CX nor gate count falls, and runs each pass
of Qiskit 2.5.2's `generate_preset_pass_manager(3, basis_gates=[rx, ry, rz, cx, p])` alone on
that fixed point, followed by the preset's translation stage. The script's docstring defines
the rows and columns.

```
cd bridge
uv run python -I ../bench/qrunch/qiskit_passes.py qrisp            # qrisp-{base,passes,reverse}.tsv
uv run python -I ../bench/qrunch/qiskit_passes.py --snap qrisp     # snap-qrisp-*.tsv
```

`<suite>-base.tsv` gives catq-compile's figures after one run and at its fixed point;
`<suite>-passes.tsv` one row per circuit and pass, with the differences from the fixed point;
`<suite>-reverse.tsv` catq-compile on Qiskit's output. The `snap-` files take as base the fixed
point reached after printing the circuit with `qasm2.dumps`, which writes an angle within 1e-12
of a rational multiple of π as that multiple. Every changed output equals its input up to a
global phase (`Operator.equiv` up to 10 qubits, one random statevector up to 20 qubits; 14
circuits above 20 qubits or with mid-circuit measurements are `nosim`), and no check failed.

Totals over the 62 circuits, differences from catq-compile's fixed point (negative: the pass
lowers the figure):

| Pass | CX | Two-qubit depth | Gates | Circuits with fewer gates |
|---|---|---|---|---|
| Optimize1qGatesDecomposition | 0 | 0 | −517 | 15 |
| CommutativeCancellation | −16 | −9 | −38 | 2 |
| TwoQubitPeepholeOptimization | −7 | −1 | −25 | 3 |
| RemoveIdentityEquivalent | 0 | 0 | −18 | 3 |
| RemoveDiagonalGatesBeforeMeasure | 0 | 0 | −188 | 1 |
| ConsolidateBlocks (with Split2QUnitaries) | −7 | −1 | +193 | 0 |
| InverseCancellation, ContractIdleWiresInControlFlow | 0 | 0 | 0 | 0 |
| optimization stage | −32 | −12 | −555 | 15 |
| whole preset without ElidePermutations | −32 | −12 | −617 | 14 |
| snapping the angles, then catq-compile | −25 | −11 | −62 | 2 |
| ElidePermutations on the input, then catq-compile | −49 | −13 | +216 | 3 |

The CX differences come from two rows. On Shor's order finding (7 mod 15) catq-compile stops at
1308 CX, and snapping the angles, or any pass that perturbs them, leads it to 1283, Qiskit's
figure without ElidePermutations; the decimal angles of Qrisp's circuit are read as exact
rationals near, but not equal to, multiples of π, which blocks exact cancellation. On the
mid-circuit-measurement row two-qubit block resynthesis removes 7 CX. After snapping, the whole
preset lowers no CX on any unitary circuit; it removes gates only, by shortening three-gate
one-qubit runs. Eliding SWAPs on the input removes 6 CX on QPE, 12 on QFT, 12 on Shor and 19 on
the mid-circuit row.

In the reverse direction catq-compile lowers no CX count of Qiskit's outputs; it removes 1,163
gates in total (lower on 27 circuits, higher on 30).
