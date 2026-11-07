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
OpenQASM 2 ─read─▶ qelib1 statements ─elide swaps─▶ ─snap angles─▶
  ─lower─▶ gates over exact angles ─Level 2─▶ ─KAK on two-qubit blocks─▶
  ─ZYZ/XYX on one-qubit runs─▶ ─Qrunch basis─▶ ─fuse─▶ ─commute back across cx─▶
  ─Clifford frame─▶ ─shorten one-qubit runs─▶ ─fuse─▶ OpenQASM 2, phase and permutation
```

Swap statements are removed and the statements after them relabelled; the permutation is
returned with the phase ([`qelibListMatrix_elideQ`](CatCrypt/Quantum/SwapElide.lean)). An angle
within 10⁻¹² of a multiple of π/16 read from a decimal is replaced by that multiple, and the
distance moved enters the bound
([`norm_qelibListMatrix_snapQ_sub_le`](CatCrypt/Quantum/AngleSnap.lean)). The statements after
the last pass are the input of the next round. Rounds repeat while the CX count, or at equal CX
count the statement count, falls, at most eight times (`--rounds k`); the bounds of the rounds
add up, and so do their exact phases
([`norm_runRounds_sub_le`](CatCrypt/Quantum/QrunchRound.lean)), and the whole run satisfies
`M_in ≈ P_π · e^{i·phase} M_out` within the snapping bound plus the bounds of the rounds
([`norm_runCompile_sub_le`](CatCrypt/Quantum/QrunchRound.lean)). The bridge applies π by
relabelling later operations and the qubits final measurements read, and appends a swap
network where neither absorbs it.

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
- A gate list of our own programs is exported as OpenQASM 2 text, and reading that text back
  gives statements whose matrix is the gate list's matrix times an exact phase
  ([`listMatrix_importGates_exportQASM`](CatCrypt/Quantum/QrunchExport.lean)); `lake exe
  catq-export` writes the QFT, phase estimation and amplitude amplification circuits to
  [`bench/qasm/catcrypt/`](bench/qasm/catcrypt/).

## Measurements

Against Qiskit's `transpile` at optimization level 3 into the same basis, measured by
[`bench/qrunch/compare.py`](bench/qrunch/compare.py) and recorded in
[`bench/qrunch/`](bench/qrunch/); gates and time are ratios ours/Qiskit.

| Suite | Circuits (qubits) | CX count and two-qubit depth | Gates | Time |
|---|---|---|---|---|
| Q-Synth VQE | 12 (8–16) | equal on all | 0.85–1.01, below on 11 | median 1.9 |
| Nam | 30 (5–192) | equal on all | 0.91–1.01, below on 16 | median 0.9 |
| QASMBench small | 12 (2–5) | equal on all | 0.53–1.05, below on 8 | median 0.2 |
| Our programs (`catq-export`) | 5 (2–6) | equal on all | 0.46–1.00, below on 2 | median 0.75 |
| Qrisp's algorithms, with the layout option | 7 (5–13) | equal on all | 0.62–1.02, below on 5 | median 2.4 |

Times are rough: the runs shared the machine with Lean builds, and catq-compile runs up to eight
rounds. The Qrisp rows are in [`bench/qrunch/qrisp/`](bench/qrunch/qrisp/); after routing onto IQM
and IBM coupling maps the CX counts and expected success probabilities of the two compilers agree
within the router's variance ([`bench/qrunch/hw-metrics/`](bench/qrunch/hw-metrics/)).

## What is trusted

Qiskit's reading and writing of OpenQASM 2 in the bridge, the segmentation at barriers and at
measurements, resets and classically controlled operations, and the printing in
[`bridge/catq/qasm_io.py`](bridge/catq/qasm_io.py), the Lean compiler and runtime
that run `catq-compile`, and the executable
[`compileFile`](CatCrypt/Quantum/Benchmark/QrunchCompile.lean), which reads and writes the files
and prints the exact phase in floating point; the composition of the stages within a round is
proved ([`norm_round_sub_le`](CatCrypt/Quantum/QrunchRound.lean)). Without `--check` the fits
are not checked and the bound is reported as `unchecked`.

## Programs in the Qrisp-like layer

Programs can also be written in Lean, in XQPL with the constructs of Qrisp, and exported to
`catq-compile`. A program's operations come with exact gate lists
([`OpGateList`, `OpGates`](CatCrypt/Quantum/XQPLGates.lean)); every such program lowers to QPL
with its denotation kept ([`lowerXQPL_denote`](CatCrypt/Quantum/XQPLGates.lean)), and HQPL's
register operations are one instance. On measurement-free programs:

- `adjoint`, `controlled` and `conjGates` have the matrices of the inverse, the controlled
  unitary and U·V·U† ([`unitary_adjoint`](CatCrypt/Quantum/XQPLGates.lean),
  [`unitary_controlled`](CatCrypt/Quantum/XQPLGates.lean),
  [`listMatrix_conjGates`](CatCrypt/Quantum/XQPLGates.lean)); control is defined on the exact
  matrix, which the channel of a program does not determine.
- A predicate computed into a clean ancilla, used as a control and uncomputed, applies the
  body where the predicate holds and restores the ancilla, also when the compute step adds a
  diagonal phase, as the relative-phase Toffoli does
  ([`listMatrix_predAncilla_conj`](CatCrypt/Quantum/AndAncilla.lean),
  [`listMatrix_rtofGates`](CatCrypt/Quantum/AndAncilla.lean)); `mcontrolled` and `with r == v`
  are its instances ([`unitary_mcontrolled`](CatCrypt/Quantum/XQPLEnv.lean),
  [`unitary_withEq`](CatCrypt/Quantum/XQPLEnv.lean)).
- Typed registers place gate lists on their qubits and read basis states as values
  ([`listMatrix_place`](CatCrypt/Quantum/QRegister.lean)); measuring a register on a basis
  state returns its value with probability one
  ([`measReg_trace_basisState`](CatCrypt/Quantum/QRegisterMeas.lean)).
- Uncomputation has a Boolean qfree and permeable check on reversible atoms; a computation
  that passes it is undone by its inverse with the ancilla restored
  ([`computes_of_check`](CatCrypt/Quantum/Uncomputation.lean),
  [`unitary_uncompute`](CatCrypt/Quantum/XQPLEnv.lean)).
- The exported text of a program reads back as its matrix times an exact phase
  ([`qelibListMatrix_export_xqpl`](CatCrypt/Quantum/XQPLEnv.lean)).

Qrisp programs themselves reach `catq-compile` through the adapter of the bridge
([`bridge/catq/qrisp_adapter.py`](bridge/catq/qrisp_adapter.py)).

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
