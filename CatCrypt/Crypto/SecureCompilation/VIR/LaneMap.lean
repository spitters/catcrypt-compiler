/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.BitVec

/-!
# Verified vectorization core: lane-parallel MAP = sequential scalar map

This is the **denotation-preservation heart** for the *lane-parallel-map* mode of
the verified vectorizer — the structural sibling of `VectorReduce`. Where
`VectorReduce` covers horizontal *reductions* (one length-`L` accumulation
collapsed to a packed lane-wise op + horizontal `hsum`, sound over any
`AddCommMonoid`), this file covers lane-parallel *maps*: a per-lane independent
function `f : α → β` applied lane-by-lane to a packed vector `(a₀,…,a_{L-1})` is
the same as running `f` sequentially on each lane.

Independence per lane (no cross-lane dependency in `f`) means the equality is
*structural* — `funext` on the lane index reduces both sides to `f (v i)`. So
the theorem holds **at any lane type whatsoever** (no algebra needed), which is
exactly the reusable shape we want for SIMD primitives whose lanes don't
combine: ChaCha20 quarter-round (4× independent blocks, `__m128i` or `__m256i`
two-block layout), Keccak per-lane rotations (`ρ` step, `Fin 25` independent
rotates by lane-specific constants), Poseidon2 S-box (`x → x^5` applied to each
state slot independently), Salsa20 quarter-round, BLAKE2 column/diagonal step,
etc.

The vectorized emit's denotation is the *packed* form `laneMap f v` (an L-tuple
where each lane independently applies `f`); the scalar emit's denotation is the
sequential per-lane fold `fun i => f (v i)`. `laneMap_eq_scalarMap` says these
are equal — no `AddCommMonoid` needed, no associativity/commutativity rewriting.

(Contrast with `VectorReduce.scalarFold_eq_hsum`, which DOES need
associativity+commutativity because the horizontal reduction *reassociates and
reorders* the scalar fold. The lane-map mode is *strictly easier*: no
reassociation, only "definition unfolds to definition".)

This file does not import `VectorReduce`: the two are independent vectorizer
primitives. New emit modes that use lane-map (`emitChachaVecJazz`) reference
`laneMap_eq_scalarMap`; emit modes that use reduce (`emitFrodoVecJazz`)
reference `scalarFold_eq_hsum`. The eventual full vectorizer composes the two
(per-lane MAP + horizontal REDUCE).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LaneMap

variable {α β : Type*} {L : ℕ}

/-- The lane-parallel MAP: applying a per-lane independent function `f` to each
    lane of a packed vector. This is the **packed** denotation a SIMD-MAP op
    realizes (an AVX2 lane-wise op + lane-local registers; no cross-lane
    routing). The L lanes are computed "in parallel" by the hardware, but the
    mathematical denotation is just `f` applied at every lane. -/
def laneMap (f : α → β) (v : Fin L → α) : Fin L → β := fun i => f (v i)

/-- The scalar (reference) lane map: a sequential `for i = 0..L-1 { out[i] :=
    f(v[i]) }`. This is the scalar emit's denotation. -/
def scalarMap (f : α → β) (v : Fin L → α) : Fin L → β := fun i => f (v i)

/-- **Heart of the lane-parallel-map vectorizer.** The packed lane-parallel
    `laneMap f v` equals the sequential scalar map `fun i => f (v i)`. This is
    structural — independence per lane (no cross-lane dependency in `f`) means
    both sides reduce to `f (v i)` at every lane by `funext`. No algebraic
    structure on `α`/`β` is needed: the theorem holds at *any* lane type.

    Reusable for every lane-parallel-map SIMD pattern:
    - ChaCha20 4-way quarter-round (4 independent blocks, `α` = ChaCha state);
    - Keccak per-lane rotations (`α` = `BitVec 64`, `f` = per-lane rotate);
    - Poseidon2 S-box (`α` = field element, `f` = `x ↦ x^5`);
    - Salsa20 quarter-round, BLAKE2 column/diagonal step. -/
theorem laneMap_eq_scalarMap (f : α → β) (v : Fin L → α) :
    laneMap f v = scalarMap f v := by
  funext i
  rfl

/-! ## Specialization to packed `BitVec w` vectors (the ChaCha / Keccak case) -/

/-- A packed vector: `L` lanes of `w`-bit words — the semantic model of a SIMD
    register / register-group running `L` independent lanes (ChaCha 4×u32 in a
    `__m128i`; Keccak 1×u64 per lane in a `Fin 25` register file). -/
abbrev Vec (L w : ℕ) := Fin L → BitVec w

/-- Lane-wise application of a `BitVec w → BitVec w` op — the packed-SIMD MAP
    when the lane type is `BitVec w` (one AVX2 `__m256i` of `L = 256/w` lanes,
    or a SoA register group of `L` separate registers). -/
def vmap {L w : ℕ} (f : BitVec w → BitVec w) (a : Vec L w) : Vec L w :=
  fun i => f (a i)

/-- **Denotation preservation for a lane-map.** The vectorized lane-map `vmap f`
    equals the scalar straight-line per-lane map. Same content as
    `laneMap_eq_scalarMap`, specialised to `BitVec w` — the lane type of every
    SIMD lane-map emit. -/
theorem vmap_eq_scalarMap {L w : ℕ} (f : BitVec w → BitVec w) (a : Vec L w) :
    vmap f a = scalarMap f a := by
  funext i
  rfl

/-! ## Binary lane-parallel map (two-source lane op)

Many lane-parallel-map ops take two source vectors: the ChaCha quarter-round's
`a + b` / `d ^ a` / `c + d` etc. are lane-wise binary ops at width 32 (one AVX2
`VPADDD`/`VPXOR` over 4×`u32` = `__m128i`). The same structural argument: the
packed binary lane op equals the per-lane scalar binary op. -/

/-- Lane-wise binary application of a `BitVec w → BitVec w → BitVec w` op — the
    packed-SIMD MAP when both sources are packed (one AVX2 `VPADDD` /
    `VPXOR` / `VPSLLD` etc. over `L` lanes). -/
def vmap₂ {L w : ℕ} (f : BitVec w → BitVec w → BitVec w) (a b : Vec L w) :
    Vec L w := fun i => f (a i) (b i)

/-- The packed binary lane-map equals the per-lane scalar binary map. Structural
    — same `funext` + `rfl` as `laneMap_eq_scalarMap`. -/
theorem vmap₂_eq_scalar {L w : ℕ} (f : BitVec w → BitVec w → BitVec w)
    (a b : Vec L w) :
    vmap₂ f a b = (fun i => f (a i) (b i)) := by
  funext i
  rfl

/-! ## Corollaries: instantiation stubs for the next callers

The lane-map theorem is **reusable** for every per-lane-independent SIMD
operation. We record three instantiation stubs (statements only — the actual
ops live in their per-protocol files and import this module):

* **ChaCha 4-way quarter-round** (the immediate caller of this module): each of
  the 4 SIMD lanes runs an independent quarter-round on its own 16×u32 ChaCha
  state. The lane-map theorem at `α = Fin 16 → BitVec 32`, `f =
  quarterRoundScalar`, `L = 4` gives the structural equality the emit needs.

* **Keccak per-lane rotations** (the `ρ` step): 25 independent rotates on
  `BitVec 64` lanes, each by a fixed lane-specific constant. The lane-map
  theorem at `α = BitVec 64`, `f i = (· <<< rotConst i) ||| (· >>> (64 -
  rotConst i))`, `L = 25`. (Strictly: `f` depends on the lane index, so the
  shape is `laneMap` with an indexed family — see `laneMapIdx` below.)

* **Poseidon2 S-box**: `x ↦ x^5` applied to each state slot. The lane-map
  theorem at `α = ZMod p` (or the abstract field), `f = (· ^ 5)`, `L = state
  width`.

The three stubs below are statement-only `theorem` shapes — they instantiate
`laneMap_eq_scalarMap` at the specific lane type and `f`. They are NOT proved
here (the per-protocol emit files will discharge them by `rfl` via the core
theorem); they document the reusable shape. -/

/-- Lane-indexed map: `f` may depend on the lane index `i` (Keccak's `ρ` rotates
    each lane by a *different* constant — `f i x = rotL x (rotConst i)`). The
    same structural equality holds. -/
def laneMapIdx (f : Fin L → α → β) (v : Fin L → α) : Fin L → β :=
  fun i => f i (v i)

/-- The lane-indexed map equals the sequential per-lane scalar map — same
    `funext + rfl` argument. -/
theorem laneMapIdx_eq_scalar (f : Fin L → α → β) (v : Fin L → α) :
    laneMapIdx f v = (fun i => f i (v i)) := by
  funext i
  rfl

/-! ### ChaCha 4-way corollary (stub: full ChaCha block as a per-lane function)

This is the immediate consumer (the ChaCha20 vectorized emit). The 4-way layout
runs 4 independent ChaCha blocks in parallel, each as `α = Fin 16 → BitVec 32`
(the 16 state words). `f` is the full `chacha20BlockSpec` function. The
lane-map theorem instantiated at `L = 4`, `α = β = Fin 16 → BitVec 32` gives
the exact structural equality the emit's denotation-preservation theorem needs.
The actual `chacha20BlockSpec` lives in the ChaCha emit file (which imports
this module). -/

/-- ChaCha 4-way: a packed 4-tuple of ChaCha states, each a `Fin 16 → BitVec 32`.
    The natural SoA layout (one `__m128i` per word-lane × 16 words, i.e. 16
    `__m128i`s holding the 4 blocks' state-word `j` at lane `b`); this `Vec4`
    type captures the equivalent AoS view (4 blocks × 16 words). -/
abbrev ChaChaState := Fin 16 → BitVec 32

/-- 4-way packed ChaCha state. -/
abbrev ChaCha4Way := Fin 4 → ChaChaState

/-- **The ChaCha 4-way lane-map equality** (corollary of `laneMap_eq_scalarMap`).
    For any block function `block : ChaChaState → ChaChaState`, applying it to
    each of the 4 lanes in parallel equals running it sequentially on each lane.
    The ChaCha emit's denotation-preservation theorem instantiates this at
    `block = chachaBlockSpec`. -/
theorem chacha4way_lane_map (block : ChaChaState → ChaChaState)
    (state : ChaCha4Way) :
    laneMap block state = (fun i => block (state i)) := by
  funext i
  rfl

/-! ### Keccak corollary stub (per-lane rotations) -/

/-- The Keccak `ρ` step lane-rotation amounts (`rotConst : Fin 25 → Nat`); the
    actual table lives in the Keccak emit file. We expose only the stub shape
    here so this module compiles standalone. -/
def keccakRotStub (rotConst : Fin 25 → Nat) (state : Fin 25 → BitVec 64) :
    Fin 25 → BitVec 64 :=
  fun i => (state i) <<< (rotConst i) ||| (state i) >>> (64 - rotConst i)

/-- **The Keccak `ρ` lane-map equality** (corollary of `laneMapIdx_eq_scalar`):
    the 25 per-lane rotations are a lane-indexed map, so the packed (SIMD) form
    equals the scalar sequential form. The Keccak emit instantiates this. -/
theorem keccak_rho_lane_map (rotConst : Fin 25 → Nat)
    (state : Fin 25 → BitVec 64) :
    keccakRotStub rotConst state =
      (fun i => (state i) <<< (rotConst i) ||| (state i) >>> (64 - rotConst i)) := by
  funext i
  rfl

/-! ### Poseidon2 corollary stub (per-state-slot S-box) -/

/-- Poseidon2 per-slot S-box `x ↦ x^5` (stub; the actual field-specific S-box
    lives in the Poseidon2 emit file). -/
def poseidon2SBoxStub {n : ℕ} (state : Fin n → BitVec 64) : Fin n → BitVec 64 :=
  fun i => let x := state i; x * x * x * x * x

/-- **The Poseidon2 S-box lane-map equality** (corollary of
    `laneMap_eq_scalarMap`): applying `x ↦ x^5` to each state slot in parallel
    equals the scalar sequential map. The Poseidon2 emit instantiates this. -/
theorem poseidon2_sbox_lane_map {n : ℕ} (state : Fin n → BitVec 64) :
    poseidon2SBoxStub state =
      (fun i => let x := state i; x * x * x * x * x) := by
  funext i
  rfl

/-! ### Keccak 4-way (Simd256) corollary — whole-permutation lane map

The YMM-resident 4-way Keccak emit runs FOUR independent Keccak-p[1600,24]
permutations in parallel, one per 64-bit lane of each `__m256i` (the standard
Simd256 SoA layout: lane `i` of the 25-lane state is one `__m256i` whose four
`u64` lanes hold sponge 0..3's lane `i`). Every Keccak step — θ-parity XOR
(`vmap₂` at `^^^`), the rotate-by-1 in θ-D and the ρ rotates (`laneMapIdx` at
`rotL`), χ's `~b & c` and final XOR (`vmap₂` at `andNot`/`^^^`), ι's
round-constant XOR (`vmap₂` at `^^^` with a broadcast constant) — is applied
identically to all four sponges, so the packed form denotes four independent
scalar permutations. This is `laneMap_eq_scalarMap` at `block = the full
Keccak-p permutation`, `α = β = (Fin 25 → BitVec 64)`, `L = 4` — structurally
the ChaCha 4-way analog above. -/

/-- One Keccak-p[1600] state: 25 lanes of `u64`. -/
abbrev KeccakState := Fin 25 → BitVec 64

/-- 4-way packed Keccak state (Simd256 SoA): four sponges' 25-lane states. -/
abbrev Keccak4Way := Fin 4 → KeccakState

/-- **The Keccak 4-way lane-map equality** (corollary of `laneMap_eq_scalarMap`).
    For any permutation `perm : KeccakState → KeccakState`, applying it to each
    of the four packed sponges in parallel equals running it sequentially on
    each. The YMM 4-way emit's denotation-preservation theorem instantiates
    this at `perm = the scalar Keccak-p[1600,24] permutation`. -/
theorem keccak4way_lane_map (perm : KeccakState → KeccakState)
    (state : Keccak4Way) :
    laneMap perm state = (fun i => perm (state i)) := by
  funext i
  rfl

end CatCrypt.Crypto.SecureCompilation.VIR.LaneMap
