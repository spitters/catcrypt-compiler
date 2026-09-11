/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.StructuredControlFlow
public import CatCrypt.Crypto.SecureCompilation.VIR.StructuredControlFlow
public meta import CatCrypt.Crypto.SecureCompilation.VIR.DataDependentControlFlow
public import CatCrypt.Crypto.SecureCompilation.VIR.DataDependentControlFlow
public meta import CatCrypt.Crypto.SecureCompilation.VIR.ProverComposition
public import CatCrypt.Crypto.SecureCompilation.VIR.ProverComposition
public meta import CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel
public import CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel

/-!
# The fixed Fibonacci STARK prover — orchestration skeleton

This assembles the **orchestration** of the fixed BabyBear Fibonacci STARK prover
from the verified control-flow combinators (`pipeline` / `scfRepeat` / `scfWhile`),
instantiated with the p3-interop fixed-config loop counts, and proves the skeleton's
denotation is the explicit phase sequence — each loop the n-fold iterate of its body.

**Honest scope.** This proves the *orchestration sequencing* is correct: the phase
BODIES are parameters (`ProverLeaves`), the slots the owned-emitted leaves plug into
— the Poseidon2 permutation / 2-to-1 compressor (already single owned `.s`), the
NTT/LDE column step, the FRI fold, the per-query opening. What this is NOT: the
phases are not yet instantiated with those emitted leaves, the AIR/trace-generation
front is not owned-emitted, and there is no single-`.s` emit + KAT of the composite.
Those are the remaining Gap-2 work. What IS delivered: the prover's loop/sequence
structure is now a composition of verified combinators with a denotation, so plugging
in the emitted leaf bodies yields a prover whose orchestration is correct by
construction (`fibProver_denote`), and a looped phase is provably the iterate of its
emitted body (via `LoopEmitBridge.loopEmit_denote_iterate`, on the machine side).
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.FibProverSkeleton

open CatCrypt.Crypto.SecureCompilation.VIR.StructuredControlFlow
open CatCrypt.Crypto.SecureCompilation.VIR.ProverComposition

set_option autoImplicit false

/-! ## 1. The fixed p3-interop configuration (the constant loop bounds)

The fixed Fibonacci AIR under the p3 interop config: BabyBear, width 2, trace
height 8, `log_blowup = 2` (so the LDE domain is `8 << 2 = 32`), `log_final_poly_len
= 2`, `max_log_arity = 1` (arity-2 FRI folds), 8 FRI queries, 0 PoW bits. Because
the statement is fixed, every loop bound is a compile-time constant — exactly what
the counted-loop combinator (`scfRepeat`) needs.

**Faithfulness.** These counts are read off the working crate's prover
(`crates/catcrypt-plonky3/src/prover.rs`), whose `prove()` is byte-identical to and
accepted by the genuine p3 0.5.3 prover/verifier — not guessed:
`trace = [[_;2];8]` ⇒ width 2, height 8; `lde/ctrace = [[_;2];32]` ⇒ committed width
2 over a domain of 32 rows; the Merkle tree is "up to 32 leaves"; FRI folds the
size-32 (log 5) codeword down to `log_final_poly_len = 2` (final length 4), i.e.
`5 − 2 = 3` arity-2 fold rounds; 8 queries. The model abstracts (states explicitly):
the quotient-column LDEs and the per-FRI-round Merkle commits are folded into the
`friFold` phase rather than separate loops, and `merkleStep` counts the leaf-row
hashes (the dominant Merkle cost); the binary-tree internal compressions
(`numLeaves − 1`) are part of the same commit phase. -/

/-- Trace height (rows) of the Fibonacci AIR. -/
def traceHeight : Nat := 8
/-- LDE domain size: `traceHeight << log_blowup` with `log_blowup = 2`. -/
def ldeSize : Nat := 32
/-- Committed trace columns (Fibonacci width 2; `ctrace = [[_;2];32]` in the crate). -/
def numCols : Nat := 2
/-- Merkle leaves over the LDE domain (one per LDE row). -/
def numLeaves : Nat := ldeSize
/-- FRI fold rounds: `log2 ldeSize − log_final_poly_len = 5 − 2 = 3` arity-2 folds. -/
def friRounds : Nat := 3
/-- FRI query openings. -/
def numQueries : Nat := 8

/-! ## 2. The phase bodies (parameters — the owned-emitted leaves plug in here) -/

/-- The prover's phase steps over an abstract prover state `σ`. Each field is a
    state-transformer; the looped phases iterate a single-step body. The
    owned-emitted leaves instantiate these:
    `traceGen`/`serialize` are one-shot; `ldeStep` is one NTT/LDE column (looped
    over `numCols`); `merkleStep` is one Poseidon2 2-to-1 compression (looped over
    `numLeaves`); `friFold` is one FRI fold round (looped over `friRounds`);
    `queryStep` is one query opening (looped over `numQueries`). -/
structure ProverLeaves (σ : Type) where
  traceGen   : σ → σ
  ldeStep    : σ → σ
  merkleStep : σ → σ
  friFold    : σ → σ
  queryStep  : σ → σ
  serialize  : σ → σ

/-! ## 3. The prover orchestration, composed from the verified combinators -/

/-- The fixed Fibonacci prover orchestration: trace-gen, then the column-LDE loop,
    the Merkle-commit loop, the FRI fold loop, the query loop, then serialize — a
    `pipeline` of phases, each looped phase an `scfRepeat` with the fixed count. -/
def fibProver {σ : Type} (L : ProverLeaves σ) : σ → σ :=
  pipeline
    [ L.traceGen
    , scfRepeat numCols L.ldeStep
    , scfRepeat numLeaves L.merkleStep
    , scfRepeat friRounds L.friFold
    , scfRepeat numQueries L.queryStep
    , L.serialize ]

/-- **The prover skeleton's denotation is the explicit phase sequence.** Running
    `fibProver` is exactly: trace-gen, then the LDE step iterated `numCols` times,
    the Merkle step iterated `numLeaves` times, the FRI fold iterated `friRounds`
    times, the query step iterated `numQueries` times, then serialize — composed
    left to right. The orchestration sequencing + every loop bound is correct by
    construction; the emitted leaf bodies plug into the `L.*` slots. -/
theorem fibProver_denote {σ : Type} (L : ProverLeaves σ) (s : σ) :
    fibProver L s
      = L.serialize
          ((L.queryStep^[numQueries])
            ((L.friFold^[friRounds])
              ((L.merkleStep^[numLeaves])
                ((L.ldeStep^[numCols])
                  (L.traceGen s))))) := by
  simp only [fibProver, pipeline_cons, pipeline_nil, Function.comp_apply, id_eq,
    scfRepeat_eq_iterate]

/-! ## 4. A concrete worked instantiation over the tile leaves

Instantiate the phase bodies with `runRegBlock` tile bodies (the shape the real
owned leaves take) and check the composite reduces to the sequenced application on
a concrete state — a stand-in showing the skeleton accepts the verified-leaf body
shape. (`traceGen`/leaves here are toy accumulator bodies; the real instantiation
swaps in the emitted Poseidon2/NTT/FRI leaf bodies.) -/

open CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel

/-- A toy one-op tile body: `acc := acc + one` over a `Tile 4 32`. -/
def bumpBody : List RegInstr := [.bin .add "acc" "acc" "one"]
def bumpStep (s : TileState 4 32) : TileState 4 32 := runRegBlock s bumpBody

/-- Toy leaves: every phase is the bump step (stands in for an emitted leaf body). -/
def toyLeaves : ProverLeaves (TileState 4 32) :=
  { traceGen := bumpStep, ldeStep := bumpStep, merkleStep := bumpStep
  , friFold := bumpStep, queryStep := bumpStep, serialize := bumpStep }

/-- Initial tile state: `acc = 0`, `one = 1` (broadcast). -/
def toyInit : TileState 4 32 :=
  { regs := fun r => if r = "one" then (fun _ => 1) else fun _ => 0 }

/-- **KAT: the composed prover skeleton applies the phases in sequence.** With the
    toy bump leaves, `fibProver` applies `bumpStep` exactly
    `1 + numCols + numLeaves + friRounds + numQueries + 1` times
    (`= 1+2+32+3+8+1 = 47`), so every lane of `acc` ends at 47 — confirming the
    pipeline + the five `scfRepeat` loop counts (the real p3 config) compose to the
    right total. -/
theorem fibProver_toy_kat :
    ((fibProver toyLeaves toyInit).get "acc" 0 = 47)
      ∧ ((fibProver toyLeaves toyInit).get "acc" 3 = 47) := by
  native_decide

/-! ## 5. The trace-generation phase made REAL (the Fibonacci recurrence)

`traceGen` is the one prover phase that is "Rust glue baked to the Fibonacci
constraints" in the crate — but it is just the width-2 Fibonacci recurrence over 8
rows, a bounded `scfRepeat`. Here it is a **real** verified phase body (not the toy
bump): `fibStep (a, b) = (b, a + b)` over BabyBear, and looping it produces the trace
whose final value is the public input `F₈ = 21` (`FIB_PUBLIC_VALUES = [0, 1, 21]`).
This is the first `ProverLeaves` slot filled with the actual AIR computation, KAT'd
against the real public value (not a fabricated one). -/

/-- The Fibonacci recurrence step over a BabyBear pair `(a, b) ↦ (b, a + b)`. (The
    intermediate values stay `< p`, so the bare `BitVec 32` add is the field add.) -/
def fibStep (p : BitVec 32 × BitVec 32) : BitVec 32 × BitVec 32 := (p.2, p.1 + p.2)

/-- The Fibonacci trace-gen as a structured loop: 7 steps from the seed `(F₀, F₁) =
    (0, 1)` yields `(F₇, F₈) = (13, 21)`. (The 8-row trace's rows are the successive
    pairs; `scfRepeat`/`scfFor` is exactly the row loop.) -/
def fibTraceGen : BitVec 32 × BitVec 32 := scfRepeat 7 fibStep (0, 1)

/-- **The real trace-gen produces the public value `F₈ = 21`.** The seed `(0, 1)`
    are `FIB_PUBLIC_VALUES[0], [1]`; the loop's final second component is
    `FIB_PUBLIC_VALUES[2] = 21`. So the `scfRepeat` trace-gen phase computes the
    actual Fibonacci public output — the AIR's trace generation, owned and verified,
    not Rust glue. -/
theorem fibTraceGen_public_value : fibTraceGen = (13, 21) := by native_decide

/-- The trace-gen instantiates `ProverLeaves.traceGen` over a prover state carrying
    the `(a, b)` pair: one real phase body filled in (the others await their emitted
    leaves). The phase advances the pair by the recurrence (here as the seed→trace
    map applied once at the state's pair). -/
def fibStateTraceGen : (BitVec 32 × BitVec 32) → (BitVec 32 × BitVec 32) :=
  scfRepeat 7 fibStep

/-- `fibStateTraceGen` from the seed is the trace-gen value — the phase, run on the
    initial prover state, yields the public-value-bearing trace. -/
theorem fibStateTraceGen_seed : fibStateTraceGen (0, 1) = (13, 21) := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.FibProverSkeleton
