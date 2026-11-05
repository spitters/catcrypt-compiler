# QASMBench circuits

The `small/` files are copied verbatim from
[github.com/pnnl/QASMBench](https://github.com/pnnl/QASMBench) and carry that
project's copyright; `LICENSE` is its licence file, reproduced as that licence
requires.

`bench/qrunch/compare.py` compares `catq-compile` with Qiskit on them:

```
cd bridge && uv run python -I ../bench/qrunch/compare.py --out results-qasmbench.tsv ../bench/qasm/qasmbench/small/*.qasm
```
