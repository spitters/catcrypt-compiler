# The Qrunch circuit compiler

`catq-compile` optimizes quantum circuits for Kvantify's Qrunch platform. It reads an
OpenQASM 2 file, optimizes and resynthesizes the circuit in Lean over exact angles, and writes
an OpenQASM 2 file over the Qrunch basis {rx, ry, rz, cx, p} together with the global phase that
relates the two. Each stage has a Lean theorem about the matrix of the circuit it returns.

## The main theorem

The resynthesis level returns gates whose matrix is within a computed bound ε of the unitary of
the input circuit, up to a computed global phase, in the operator norm
([`norm_listMatrix_resynth_sub_le`](CatCrypt/Quantum/Optimization/ResynthLevel.lean)), and has
at most as many CNOTs as its input
([`cnotCount_resynth_out_le`](CatCrypt/Quantum/Optimization/ResynthLevel.lean)). The bound
holds for every input, whatever the floating-point fits return.

## The pipeline

```
OpenQASM 2 ─read─▶ qelib1 statements ─lower─▶ gates over exact angles ─Level 2─▶
  ─KAK on two-qubit blocks─▶ ─ZYZ/XYX on one-qubit runs─▶ ─Qrunch basis─▶
  ─fuse─▶ ─commute back across cx─▶ ─Clifford frame─▶ ─fuse─▶ OpenQASM 2 and phase
```

## Main ideas

Every angle is a + bπ with rational a and b. The rewriting passes therefore add and compare
angles exactly, and their theorems are equalities of matrices.

The KAK and ZYZ angles come from floating-point fits, which the compiler does not trust. With
`--check` a checker on complex ball arithmetic bounds the distance between each block and its
replacement, and the bound of the level is the sum of the checked bounds; a fit within 10⁻¹² of
a multiple of π/4 is taken as that exact angle.

The output passes keep a pending rotation per qubit. Rotations about one axis merge; a rotation
that commutes with a cx passes through it in either direction; rotations by multiples of π/2
collect into a one-qubit Clifford frame, computed exactly over ℤ[e^{iπ/4}], through which the
other rotations are conjugated.

## What is proved

- Each qelib1 statement is lowered to gates whose matrix is its qelib1 matrix times an exact
  phase ([`listMatrix_lowerQ`](CatCrypt/Quantum/Qelib.lean)), and the reader on bytes returns
  what the reader on characters returns, for ASCII sources
  ([`importQB_eq`](CatCrypt/Quantum/OpenQASMBytes.lean)).
- Every pass of Level 2 preserves the matrix of the circuit exactly, not only its channel
  ([`runNamed_level2_matrixCorrect`](CatCrypt/Quantum/Optimization/MatrixSound.lean)).
- Replacing two-qubit blocks by KAK templates never increases the CNOT count
  ([`cnotCount_kakEmit_le`](CatCrypt/Quantum/Synthesis/KAKPassSmall.lean)), and behind the
  checker it moves the matrix by at most the sum of the checked bounds, up to the sum of the
  checked phases ([`listMatrix_kakEmit_checkedFit`](CatCrypt/Quantum/Synthesis/ApproxEmit.lean)).
- Replacing one-qubit runs by ZYZ or XYX forms keeps the CNOT count
  ([`cnotCount_zyzEmit`](CatCrypt/Quantum/Synthesis/ZYZPass.lean)) and satisfies the same bound
  behind the checker
  ([`listMatrix_zyzEmit_checkedZFit`](CatCrypt/Quantum/Synthesis/ApproxEmit.lean)).
- The number the checker returns bounds the operator norm of the difference between a block and
  its replacement ([`norm_sub_le_checkPair`](CatCrypt/Quantum/Synthesis/GateBall.lean)).
- The translation into the Qrunch basis has the matrix of its input times an exact phase
  ([`qelibListMatrix_toQelib`](CatCrypt/Quantum/QrunchBasis.lean)).
- Fusion, backward commutation and the Clifford frame each keep the matrix exactly, up to the
  phase they return, keep the CX count and do not lengthen the program
  ([`qelibListMatrix_fuseQ`](CatCrypt/Quantum/QrunchFuse.lean),
  [`qelibListMatrix_commuteQ`](CatCrypt/Quantum/QrunchCommute.lean),
  [`qelibListMatrix_pauliQ`](CatCrypt/Quantum/QrunchFuse.lean),
  [`cxCount_pauliQ`](CatCrypt/Quantum/QrunchFuse.lean),
  [`length_pauliQ_le`](CatCrypt/Quantum/QrunchFuse.lean)).

## Measurements

Against Qiskit's `transpile` at optimization level 3 into the same basis, best of five runs per
circuit, measured by [`bench/qrunch/compare.py`](bench/qrunch/compare.py) and recorded in
[`bench/qrunch/`](bench/qrunch/); gates and time are ratios ours/Qiskit.

| Suite | Circuits (qubits) | CX count and two-qubit depth | Gates | Time |
|---|---|---|---|---|
| Q-Synth VQE | 12 (8–16) | equal on all | 0.85–1.01, below on 11 | median 0.78 |
| Nam | 30 (5–192) | equal on all | 0.91–1.01, below on 16 | median 0.47 |
| QASMBench small | 12 (2–5) | equal on all | 0.53–1.05, below on 8 | median 0.10 |

## What is trusted

Qiskit's reading and writing of OpenQASM 2 in the bridge, the segmentation at barriers and at
measurements, resets and classically controlled operations, and the printing in
[`bridge/catq/qasm_io.py`](bridge/catq/qasm_io.py), the Lean compiler and runtime
that run `catq-compile`, and the executable
[`compileFile`](CatCrypt/Quantum/Benchmark/QrunchCompile.lean), which composes the stages and
adds their phases in floating point. Without `--check` the fits are not checked and the bound is
reported as `unchecked`.

## Where the code is

The reader is [OpenQASMBytes](CatCrypt/Quantum/OpenQASMBytes.lean), specified by the character
reader of [OpenQASMImport](CatCrypt/Quantum/OpenQASMImport.lean); [Qelib](CatCrypt/Quantum/Qelib.lean)
gives each qelib1 statement its matrix and its lowering. Level 2 is a list of named passes in
[PassPipeline](CatCrypt/Quantum/Optimization/PassPipeline.lean), with their matrix theorems in
[MatrixSound](CatCrypt/Quantum/Optimization/MatrixSound.lean). The resynthesis level is
[ResynthLevel](CatCrypt/Quantum/Optimization/ResynthLevel.lean): the KAK templates are in
[KAK](CatCrypt/Quantum/Synthesis/KAK.lean) and [KAKSmall](CatCrypt/Quantum/Synthesis/KAKSmall.lean), the
block pass in [KAKPassSmall](CatCrypt/Quantum/Synthesis/KAKPassSmall.lean), the one-qubit pass in
[ZYZPass](CatCrypt/Quantum/Synthesis/ZYZPass.lean), and the floating-point fits in
[KAKFloat](CatCrypt/Quantum/Synthesis/KAKFloat.lean) and [QrunchFit](CatCrypt/Quantum/Synthesis/QrunchFit.lean).
The checker is built from complex balls in fixed-point dyadics
([CBall](CatCrypt/Quantum/Synthesis/CBall.lean)), enclosures of e^{iθ} at exact angles
([ExpIBall](CatCrypt/Quantum/Synthesis/ExpIBall.lean)) and the per-block bound of
[GateBall](CatCrypt/Quantum/Synthesis/GateBall.lean); [ApproxEmit](CatCrypt/Quantum/Synthesis/ApproxEmit.lean)
adds the bounds over blocks. The output passes are [QrunchBasis](CatCrypt/Quantum/QrunchBasis.lean),
[QrunchFuse](CatCrypt/Quantum/QrunchFuse.lean) and [QrunchCommute](CatCrypt/Quantum/QrunchCommute.lean).

## Try it

```
lake build catq-compile
lake exe catq-compile bench/qasm/qsynth/simple_8q_50o_0.qasm out.qasm 2r --check
cd bridge && uv run python -I ../bench/qrunch/compare.py
```

[`bridge/README.md`](bridge/README.md) describes the adapter to Qrunch's `Compiler` protocol
and the adapter for Qrisp programs, whose trusted base adds Qrisp's decomposition and
conversion to Qiskit; [`bench/qrunch/qrisp/`](bench/qrunch/qrisp/) measures Qrisp's QPE, Shor,
QAOA, VQE, Grover, QFT and Dicke-state circuits.
The Q-Synth and QASMBench circuits are in [`bench/qasm/`](bench/qasm/);
[`bench/qrunch/fetch-nam.sh`](bench/qrunch/fetch-nam.sh) downloads the Nam circuits.
