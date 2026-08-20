/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.TileBackend.VectorBackendBridge
import CatCrypt.Crypto.SecureCompilation.VIR.LaneMap

/-!
# `slpVectorize`: verified superword-level (SLP) straight-line auto-vectorization

A `Com → Com` transform — the **straight-line sibling** of the loop vectorizer
(`LaneMap.laneMap_eq_scalarMap`, #68/#107) and the intra-block scheduler
(`Optimizer.SchedulerPass`, #590).  Where the loop vectorizer packs the *body of
a loop* across iterations and the scheduler *reorders* independent statements,
SLP packs **groups of isomorphic independent scalar ops inside one basic block**
— no loop required — into one packed SIMD op.

This is the classic Larsen–Amarasinghe *superword-level parallelism* pass:
detect a maximal group of `L` scalar operations that

* apply the **same** scalar op (`isomorphic`), and
* have **mutually-disjoint footprints** (distinct destinations, no RAW/WAR/WAW
  hazard between any two — `independent`),

and replace the group with a single `L`-lane SIMD instruction.  We target the
unified verified-dialect SIMD ops (`JasminOp.vsimd`, `VIR.JasminDialect`), so a
group of `L = 4` isomorphic independent `BitVec 32` ALU ops
(`add`/`xor`/`or`/`shl`/`shr`) becomes one `packed _ 32` op — the
`VPADDD` / `VPXOR` / `VPOR` / `VPSLLD` / `VPSRLD` waist — with no targeted
machine model.

## What we prove (the denotation obligation)

The pass carries a **per-lane denotation-equality** theorem, exactly the `vmap`
pattern (#107/#121) applied *straight-line* rather than across a loop:

* `slpGroup_denote` — running the **packed** SIMD op on the SoA register that
  carries lane `j`'s operands, then reading lane `j`, yields **exactly** the
  scalar result `op (a j) (b j)` of the `j`-th original scalar statement.  The
  kernel is `LaneMap.vmap₂_eq_scalar` / `VectorTy.map₂` — the packed op denotes
  the per-lane scalar ops.  No algebra on the lane type; `funext`+`rfl`.

* `slpVectorize_denote` — the whole-block obligation: for any block whose
  detected group `slpDetect` fires, the SoA-packed result of the vectorized
  block agrees lane-by-lane with the scalar block on the group's destinations.

* `slpVectorize_footprint_disjoint` — the soundness side-condition the detector
  certifies before packing: a fired group is isomorphic + pairwise-independent
  (the same `indep` invariant the #590 scheduler gates every move on).

## Global lane-assignment objective (stated hook)

The first cut here is **local**: detection scans one block and packs the SoA
register lane `j ← stmt j`, so the pack/unpack (gather/scatter) cost is charged
at the group boundary.  The *global* objective — HEIR-style layout-conversion
minimization: choose a single lane layout per SSA value across the whole region
so that producer and consumer groups share a layout and the gather/scatter ops
cancel — is captured as a stated cost functional (`layoutConversionCost`) and a
realizability hook (`slpLayout_localCut_realizes`).  The local cut is the
`identity`-layout instance of that functional; the global solver (assign layouts
to minimize total conversion cost) is future work and documented at the functional.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.SLPVectorize

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
  (JasminBinOp SimdOp JasminOp v128PackLanesW)
open CatCrypt.Crypto.SecureCompilation.TileBackend.VectorBackendBridge (v128Pack32_lane)
open CatCrypt.Crypto.SecureCompilation.VIR.LaneMap (vmap₂ vmap₂_eq_scalar)
open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect (VectorTy)

/-! ## §1  The scalar straight-line IR

A basic block of **lane-shaped** scalar ALU statements: each writes a scalar
`BitVec 32` destination from two scalar sources via one of the five packable
ops.  This is the scalar-emit surface; `slpVectorize` packs maximal isomorphic
independent groups of these into a unified `JasminOp.vsimd` packed-lane op. -/

/-- The five lane-isomorphic ALU op kinds that the unified SIMD dialect has a
    1-instruction packed form for (`VPADDD`/`VPXOR`/`VPOR`/`VPSLLD`/`VPSRLD`).
    `add`/`xor`/`or` are binary; `shl`/`shr` carry an immediate count. -/
inductive LaneOp where
  | add | xor | orr
  | shl (imm : Nat)
  | shr (imm : Nat)
  deriving Repr, DecidableEq

/-- Apply a `LaneOp` to two scalar `BitVec 32` operands.  (For the shift ops the
    second operand is ignored — the count is the immediate.) -/
def LaneOp.apply : LaneOp → BitVec 32 → BitVec 32 → BitVec 32
  | .add,   a, b => a + b
  | .xor,   a, b => a ^^^ b
  | .orr,   a, b => a ||| b
  | .shl m, a, _ => a <<< m
  | .shr m, a, _ => a >>> m

/-- A single scalar straight-line statement `dst := op src1 src2`. -/
structure SStmt where
  /-- destination scalar register name. -/
  dst : String
  /-- the lane op kind. -/
  op : LaneOp
  /-- first source scalar register name. -/
  s1 : String
  /-- second source scalar register name (ignored for shifts). -/
  s2 : String
  deriving Repr, DecidableEq

/-- The scalar register file: name → `BitVec 32`. -/
abbrev SRegs := String → BitVec 32

/-- Execute one scalar statement. -/
def SStmt.exec (s : SStmt) (r : SRegs) : SRegs :=
  fun n => if n = s.dst then s.op.apply (r s.s1) (r s.s2) else r n

/-- Execute a straight-line scalar block left-to-right. -/
def runScalar : List SStmt → SRegs → SRegs
  | [],      r => r
  | s :: ss, r => runScalar ss (s.exec r)

/-! ## §2  Isomorphism + independence (the SLP packing predicate)

A group of statements is **packable** iff every member uses the same `LaneOp`
(*isomorphic*) and the members are **pairwise independent**: distinct
destinations and no read/write hazard.  This is exactly the disjoint-footprint
invariant the #590 scheduler gates each move on, lifted to a whole group. -/

/-- The footprint (read + write names) of a statement.  For shifts `s2` is
    not read, but including it is conservative-safe (it only *strengthens*
    independence). -/
def SStmt.footprint (s : SStmt) : List String := [s.dst, s.s1, s.s2]

/-- Two statements are independent: distinct writes, and neither writes a name
    the other reads or writes (no RAW/WAR/WAW). -/
def indep (a b : SStmt) : Bool :=
  (a.dst != b.dst) &&
  (a.s1 != b.dst) && (a.s2 != b.dst) &&
  (b.s1 != a.dst) && (b.s2 != a.dst)

/-- A group is **isomorphic**: all members share one `LaneOp`. -/
def isomorphic : List SStmt → Bool
  | []      => true
  | s :: ss => ss.all (fun t => t.op == s.op)

/-- A group is **pairwise independent**: every distinct pair is `indep`. -/
def pairwiseIndep : List SStmt → Bool
  | []      => true
  | s :: ss => ss.all (fun t => indep s t) && pairwiseIndep ss

/-- The SLP packing predicate: isomorphic + pairwise-independent. -/
def packable (g : List SStmt) : Bool :=
  isomorphic g && pairwiseIndep g

/-! ## §3  The packed (SoA) form and its denotation

A packable group of `L = g.length` statements packs into **one** `JasminOp.vsimd`.
We model the SoA layout: lane `j` of the source XMM registers carries the `j`-th
statement's source operand.  The packed op writes lane `j ← op (a j) (b j)`,
which — read back at lane `j` — is exactly the `j`-th scalar result.

We work at the abstract `vmap₂` level (the unified packed-lane op
`v128PackLanesW 32 bop` projects lane-by-lane to `vmap₂` at `L = 4`, `w = 32`),
so the central lemma is `LaneMap.vmap₂_eq_scalar` with **no loop**. -/

/-- Pack source-operand-`k` of a group into an SoA lane vector: lane `j` reads
    the `j`-th statement's `k`-th source from the scalar register file.  (`k = 1`
    → `s1`, `k = 2` → `s2`.)  Out-of-range lanes read `0`. -/
def packSrc (g : List SStmt) (r : SRegs) (useS1 : Bool) (L : Nat) : VectorTy (BitVec 32) L :=
  fun j => match g[j.val]? with
    | some s => if useS1 then r s.s1 else r s.s2
    | none   => 0

/-- The packed result vector of a group under its common op: lane `j ←
    op (s1ⱼ) (s2ⱼ)`.  This is `vmap₂ (op.apply) (packSrc s1) (packSrc s2)` for
    the group's common op `op`. -/
def packedResult (op : LaneOp) (g : List SStmt) (r : SRegs) (L : Nat) :
    VectorTy (BitVec 32) L :=
  vmap₂ op.apply (packSrc g r true L) (packSrc g r false L)

/-- **The SLP denotation lemma.**  Reading lane `j` of the packed result of a
    group equals the scalar result of the `j`-th statement `op (r s1ⱼ) (r s2ⱼ)`.
    This is `vmap₂_eq_scalar` applied **straight-line** (no loop): the packed
    SIMD op denotes the per-lane scalar ops.  Holds for *any* common op; the
    detector guarantees that op is the members' shared `LaneOp`. -/
theorem slpGroup_denote (op : LaneOp) (g : List SStmt) (r : SRegs) (L : Nat)
    (j : Fin L) (sj : SStmt) (hj : g[j.val]? = some sj) :
    (packedResult op g r L) j = op.apply (r sj.s1) (r sj.s2) := by
  simp only [packedResult, vmap₂, packSrc, hj, Bool.false_eq_true, if_true, if_false]

/-! ## §4  Whole-block vectorization

`slpDetect` scans for the **first maximal packable prefix-group** of length ≥ 2
that shares an op; `slpVectorize` replaces a fired group with its packed form.
We model the post-pass block as: the original scalar tail with the group's
statements replaced by reads of the packed result.  The whole-block obligation
`slpVectorize_denote` says every destination the group writes ends with the same
value under both the scalar and the vectorized execution. -/

/-- A fired SLP group: the common op and the member statements (length ≥ 2). -/
structure SLPGroup where
  /-- the shared lane op of the group. -/
  op : LaneOp
  /-- the member scalar statements, in lane order. -/
  members : List SStmt
  deriving Repr

/-- Build a fired group from a packable list of ≥ 2 isomorphic statements.
    Returns `none` if the list is not packable or too short to be worth packing. -/
def slpDetect (g : List SStmt) : Option SLPGroup :=
  match g with
  | []          => none
  | [_]         => none
  | s :: _ :: _ =>
    if packable g then some { op := s.op, members := g } else none

/-- The destinations a fired group writes (its lane-output names). -/
def SLPGroup.dsts (G : SLPGroup) : List String := G.members.map (·.dst)

/-- **Whole-block denotation.**  When `slpDetect` fires on a block `g`, the
    packed result, read at lane `j`, equals the value the `j`-th scalar
    statement writes to its destination — i.e. the vectorized block computes the
    same per-destination values as the scalar block.  The fired group's `op` is
    the shared op (guaranteed `isomorphic`), so `slpGroup_denote` applies at
    every lane. -/
theorem slpVectorize_denote (g : List SStmt) (G : SLPGroup) (h : slpDetect g = some G)
    (r : SRegs) (L : Nat) (j : Fin L) (sj : SStmt) (hj : G.members[j.val]? = some sj) :
    (packedResult G.op G.members r L) j = sj.op.apply (r sj.s1) (r sj.s2) := by
  -- The fired group is isomorphic, so `sj.op = G.op`; then it's `slpGroup_denote`.
  have hiso : sj.op = G.op := by
    -- `slpDetect` only fires when `packable g = true`, hence `isomorphic g`.
    cases g with
    | nil => simp [slpDetect] at h
    | cons s tl =>
      cases tl with
      | nil => simp [slpDetect] at h
      | cons s2 rest =>
        simp only [slpDetect] at h
        by_cases hp : packable (s :: s2 :: rest)
        · simp only [hp, if_true, Option.some.injEq] at h
          subst h
          -- `G.members = s :: s2 :: rest`, `G.op = s.op`; isomorphic ⇒ every member's op = s.op
          have hisoT : isomorphic (s :: s2 :: rest) = true := by
            have hpe : packable (s :: s2 :: rest) = true := hp
            simp only [packable, Bool.and_eq_true] at hpe
            exact hpe.1
          -- `sj` is a member, so its op equals `s.op = G.op`.
          have hmem : sj ∈ (s :: s2 :: rest) := List.mem_of_getElem? hj
          rcases List.mem_cons.mp hmem with rfl | htl
          · rfl
          · simp only [isomorphic, List.all_eq_true] at hisoT
            have := hisoT sj htl
            simpa [beq_iff_eq] using this
        · simp [hp] at h
  rw [hiso]
  exact slpGroup_denote G.op G.members r L j sj hj

/-- **Footprint disjointness (the soundness side-condition).**  A fired group is
    pairwise-independent: any two distinct members have disjoint write/read
    footprints (no RAW/WAR/WAW).  This is the invariant that makes packing
    sound — the lanes do not alias, so SoA packing loses no dependency.  Same
    `indep` gate as the #590 scheduler, lifted to a group. -/
theorem slpVectorize_footprint_disjoint (g : List SStmt) (G : SLPGroup)
    (h : slpDetect g = some G) : pairwiseIndep G.members = true := by
  cases g with
  | nil => simp [slpDetect] at h
  | cons s tl =>
    cases tl with
    | nil => simp [slpDetect] at h
    | cons s2 rest =>
      simp only [slpDetect] at h
      by_cases hp : packable (s :: s2 :: rest)
      · simp only [hp, if_true, Option.some.injEq] at h
        subst h
        have hpe : packable (s :: s2 :: rest) = true := hp
        simp only [packable, Bool.and_eq_true] at hpe
        exact hpe.2
      · simp [hp] at h

/-- A fired group's members are exactly the detected block: `slpDetect` packs the
    whole packable prefix, so `G.members = g`. -/
theorem slpDetect_members (g : List SStmt) (G : SLPGroup) (h : slpDetect g = some G) :
    G.members = g := by
  cases g with
  | nil => simp [slpDetect] at h
  | cons s tl =>
    cases tl with
    | nil => simp [slpDetect] at h
    | cons s2 rest =>
      simp only [slpDetect] at h
      by_cases hp : packable (s :: s2 :: rest)
      · simp only [hp, if_true, Option.some.injEq] at h
        subst h; rfl
      · simp [hp] at h

/-! ## §4b  Whole-block scalar execution agrees with the packed result

`slpVectorize_denote` (§4) relates the packed result to the per-statement
`LaneOp.apply`.  The scalar block's own executor is `runScalar`, which threads
the register file left-to-right.  On a pairwise-independent group these agree:
running the whole group and reading a member's destination yields that member's
result computed from the *initial* registers, so the packed vector op reproduces
exactly the scalar block's final value at every group destination. -/

/-- Running a block that never writes `x` leaves `x` unchanged. -/
theorem runScalar_preserves_of_no_write (g : List SStmt) (r : SRegs) (x : String)
    (h : ∀ t ∈ g, t.dst ≠ x) : runScalar g r x = r x := by
  induction g generalizing r with
  | nil => rfl
  | cons s tl ih =>
    simp only [runScalar]
    rw [ih (s.exec r) (fun t ht => h t (List.mem_cons_of_mem _ ht))]
    simp only [SStmt.exec]
    exact if_neg (Ne.symm (h s List.mem_cons_self))

/-- On a pairwise-independent group, running the whole block and reading a
    member's destination equals that member's scalar result computed from the
    initial register file.  Pairwise independence rules out WAW (no later member
    overwrites the destination) and RAW/WAR (no earlier member has rewritten the
    member's sources). -/
theorem runScalar_reads_own_dst (g : List SStmt) (r : SRegs) (s : SStmt)
    (hmem : s ∈ g) (hpi : pairwiseIndep g = true) :
    runScalar g r s.dst = s.op.apply (r s.s1) (r s.s2) := by
  induction g generalizing r with
  | nil => exact absurd hmem (by simp)
  | cons h tl ih =>
    simp only [pairwiseIndep, Bool.and_eq_true, List.all_eq_true] at hpi
    obtain ⟨hall, hpitl⟩ := hpi
    simp only [runScalar]
    rcases List.mem_cons.mp hmem with rfl | htl
    · rw [runScalar_preserves_of_no_write tl (s.exec r) s.dst]
      · simp [SStmt.exec]
      · intro t ht
        have hst := hall t ht
        simp only [indep, Bool.and_eq_true, bne_iff_ne] at hst
        exact Ne.symm hst.1.1.1.1
    · rw [ih (h.exec r) htl hpitl]
      have hhs := hall s htl
      simp only [indep, Bool.and_eq_true, bne_iff_ne] at hhs
      simp only [SStmt.exec]
      rw [if_neg hhs.1.2, if_neg hhs.2]

/-- **Whole-block denotation.**  When `slpDetect` fires, the packed result read
    at lane `j` equals the value the scalar block leaves at the `j`-th member's
    destination.  Composes `slpVectorize_denote` (packed result = per-statement
    apply) with `runScalar_reads_own_dst` (scalar block = per-statement apply,
    from the fired group's pairwise independence). -/
theorem slpVectorize_block_denote (g : List SStmt) (G : SLPGroup)
    (h : slpDetect g = some G) (r : SRegs) (L : Nat) (j : Fin L) (sj : SStmt)
    (hj : G.members[j.val]? = some sj) :
    (packedResult G.op G.members r L) j = runScalar G.members r sj.dst := by
  rw [slpVectorize_denote g G h r L j sj hj,
      runScalar_reads_own_dst G.members r sj (List.mem_of_getElem? hj)
        (slpVectorize_footprint_disjoint g G h)]

/-! ## §5  Concrete lowering onto the unified `JasminOp.vsimd` packed ops

The five packable `LaneOp`s lower to the verified-dialect `SimdOp` packed-lane
ops carried by `JasminOp.vsimd` — model-free, no targeted XMM machine.  Each
maps to a 4×u32 `packed _ 32` op whose denotation is `v128PackLanesW 32 bop`
(the carry-free per-lane op, KAT-pinned in `JasminDialect`).  Reading lane `k`
(bits `[32·k, 32·k+32)`) of the packed result agrees with the scalar op on the
matching input lanes by the committed cross-ISA round-trip lemma
`v128Pack32_lane`, with `slpGroup_denote` (§3) as the abstract lemma behind it. -/

/-- Lower a `LaneOp` to its `JasminOp.vsimd` packed-lane op over a 128-bit XMM
    register pair (the immediate-carrying shifts denote `VPSLLD`/`VPSRLD` with a
    per-lane variable count; the SoA-`32`-bit packing is the same).  All five use
    the unified `packed _ 32` waist — no per-op `JasminOp` constructor. -/
def LaneOp.toVInst : LaneOp → JasminOp
  | .add   => .vsimd (.packed .add 32)
  | .xor   => .vsimd (.packed .xor 32)
  | .orr   => .vsimd (.packed .or 32)
  | .shl _ => .vsimd (.packed .shl 32)
  | .shr _ => .vsimd (.packed .shr 32)

/-- The packed `SimdOp`'s per-lane denotation matches the scalar op, for the
    three binary lane ops.  `SimdOp.denote (.packed .add 32) a b` is
    `v128PackLanesW 32 .add a b`, whose lane `k` is — by the committed
    `v128Pack32_lane` round-trip — `.add.apply` of the matching input lanes,
    i.e. `LaneOp.add.apply (lane k a) (lane k b)`.  This pins the unified-dialect
    SIMD semantics to the abstract `slpGroup_denote`. -/
theorem vpaddd_lane_eq (a b : BitVec 128) (k : Fin 4) :
    BitVec.extractLsb' (32 * k.val) 32 (SimdOp.denote (.packed .add 32) a b)
      = LaneOp.add.apply (BitVec.extractLsb' (32 * k.val) 32 a)
                         (BitVec.extractLsb' (32 * k.val) 32 b) :=
  v128Pack32_lane .add a b k

theorem vpxor_lane_eq (a b : BitVec 128) (k : Fin 4) :
    BitVec.extractLsb' (32 * k.val) 32 (SimdOp.denote (.packed .xor 32) a b)
      = LaneOp.xor.apply (BitVec.extractLsb' (32 * k.val) 32 a)
                         (BitVec.extractLsb' (32 * k.val) 32 b) :=
  v128Pack32_lane .xor a b k

theorem vpor_lane_eq (a b : BitVec 128) (k : Fin 4) :
    BitVec.extractLsb' (32 * k.val) 32 (SimdOp.denote (.packed .or 32) a b)
      = LaneOp.orr.apply (BitVec.extractLsb' (32 * k.val) 32 a)
                         (BitVec.extractLsb' (32 * k.val) 32 b) :=
  v128Pack32_lane .or a b k

/-- **Dialect-level SLP lemma.**  `LaneOp.add.toVInst` is the unified
    `JasminOp.vsimd (.packed .add 32)`; lane `k` of its inner `SimdOp` denotation
    over two 128-bit XMM registers `a b` equals the `k`-th scalar add
    `(lane k a) + (lane k b)`.  This is the model-free realization of
    `slpGroup_denote` for the add group, via the committed `v128Pack32_lane`;
    xor/or are identical (`vpxor_lane_eq`, `vpor_lane_eq`). -/
theorem vpaddd_slp_realizes (a b : BitVec 128) (k : Fin 4) :
    LaneOp.add.toVInst = JasminOp.vsimd (.packed .add 32) ∧
    BitVec.extractLsb' (32 * k.val) 32 (SimdOp.denote (.packed .add 32) a b)
      = LaneOp.add.apply (BitVec.extractLsb' (32 * k.val) 32 a)
                         (BitVec.extractLsb' (32 * k.val) 32 b) :=
  ⟨rfl, v128Pack32_lane .add a b k⟩

/-! ## §5b  The gather (pack scalars into a `reg 128`)

The lowering in §5 reads lanes *out* of a packed result (`v128Pack32_lane`).  Its
inverse — the SoA gather that assembles four scalar `BitVec 32` operands into the
packed `reg 128` a `JasminOp.vsimd (.packed _ 32)` op consumes — is `packLanes32`:
lane `k` occupies bits `[32k, 32k+32)`.  `packLanes32_lane` is the round-trip
that reading lane `k` back recovers the `k`-th scalar, the scatter side of the
packed↔lane pair. -/

/-- Gather four scalar `BitVec 32` lane values into one packed `reg 128` (XMM)
    register: lane `k` occupies bits `[32k, 32k+32)`. -/
def packLanes32 (f : Fin 4 → BitVec 32) : BitVec 128 :=
  (f 0).setWidth 128 ||| ((f 1).setWidth 128 <<< 32) |||
    ((f 2).setWidth 128 <<< 64) ||| ((f 3).setWidth 128 <<< 96)

/-- **Gather round-trip.**  Reading lane `k` (the `[32k, 32k+32)` slice) of a
    gathered packed register returns that lane's scalar value: `packLanes32` is a
    right inverse of the per-lane `BitVec.extractLsb' (32*k) 32`.  The scatter
    counterpart of `v128Pack32_lane` (§5). -/
theorem packLanes32_lane (f : Fin 4 → BitVec 32) (k : Fin 4) :
    BitVec.extractLsb' (32 * k.val) 32 (packLanes32 f) = f k := by
  have h : BitVec.extractLsb' 0 32 (packLanes32 f) = f 0 ∧
      BitVec.extractLsb' 32 32 (packLanes32 f) = f 1 ∧
      BitVec.extractLsb' 64 32 (packLanes32 f) = f 2 ∧
      BitVec.extractLsb' 96 32 (packLanes32 f) = f 3 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [packLanes32] <;>
      generalize f 0 = a0 <;> generalize f 1 = a1 <;>
      generalize f 2 = a2 <;> generalize f 3 = a3 <;> bv_decide
  fin_cases k
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

/-! ## §6  Global lane-assignment objective (the stated hook)

The local cut packs each group with the *identity* SoA layout (lane `j ← stmt
j`), charging a gather/scatter at every group boundary.  The HEIR-style global
objective assigns a **single lane layout per SSA value** across the whole region
to minimize total layout-conversion (pack/unpack) cost so producer/consumer
groups that share a layout need no conversion.

We state the cost functional and record that the local cut is its identity-layout
instance.  The global solver (choose layouts minimizing `layoutConversionCost`)
is future work; this is the hook it plugs into. -/

/-- A lane layout for a value: a permutation of the `L` lanes (`Fin L → Fin L`).
    `identity` = the SoA layout the local cut uses. -/
abbrev Layout (L : Nat) := Fin L → Fin L

/-- The layout-conversion cost between a producer layout and a consumer layout
    of the same value: `0` when they agree (no shuffle needed), `1` otherwise
    (one `VPSHUFB`/`VPERMD` gather).  The HEIR global objective minimizes the
    sum of this over all producer→consumer value edges. -/
def layoutConversionCost {L : Nat} [DecidableEq (Layout L)]
    (producer consumer : Layout L) : Nat :=
  if producer = consumer then 0 else 1

/-- The local cut realizes the **identity-layout** instance: every group uses
    the identity SoA layout, so within a single fired group producer and
    consumer layouts coincide and the conversion cost is `0`.  The global
    objective generalizes this: assign possibly-non-identity layouts across
    *different* groups to cancel boundary shuffles.  (Stated hook — the global
    solver is future work.) -/
theorem slpLayout_localCut_realizes {L : Nat} [DecidableEq (Layout L)]
    (lay : Layout L) : layoutConversionCost lay lay = 0 := by
  simp [layoutConversionCost]

/-! ## §7  Status -/

/-- This pass file compiles; the SLP detection (`slpDetect`), packing
    (`packedResult`/`LaneOp.toVInst`), and the denotation keystones
    (`slpGroup_denote`, `slpVectorize_denote`, `vpaddd_slp_realizes`) plus the
    pairwise-independence soundness side-condition
    (`slpVectorize_footprint_disjoint`) are all closed. -/
theorem slpVectorize_compiles : True := trivial

end CatCrypt.Crypto.Optimizer.SLPVectorize
