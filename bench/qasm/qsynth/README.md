# Q-Synth VQE circuits

The 12 files of `Benchmarks/VQE/original` of Q-Synth (Irfansha Shaik and Jaco van de Pol),
https://github.com/irfansha/Q-Synth, commit 95a820e16ac5, copied unchanged under
the MIT licence in `LICENSE-Q-Synth`. They are OpenQASM 2 circuits of 8 and 16 qubits with
`rx`, `ry`, `rz`, `sx`, `sxdg`, `s`, `sdg`, `h`, `x` and `cx`, and angles in radians.

`bench/qrunch/compare.py` compares `catq-compile` with Qiskit on them:

```
cd bridge && uv run python -I ../bench/qrunch/compare.py
```
