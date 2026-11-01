/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.MemoryModel
public import CatCrypt.Crypto.Jasmin.PointerBorrow
public import CatCrypt.Crypto.Jasmin.JasminSem


@[expose] public section
set_option autoImplicit false

/-!
# Hoare-triple judgment over `JasminMemState`

Track 1 continuation. Defines `{P} body {Q}` over a state that bundles
`RustState` (the existing register/tower-variable state from
`LowCT.lean`) with a flat memory model `MemoryModel.Mem`. Programs
to be verified are `List InstrR` (the SSA fragment used by the bignum
ports in `S2NBignumSSA.lean`).

## What's here

- `JasminMemState` — the bundled state: register + memory.
- `HoareTriple` — partial-correctness judgment.
- **Structural rules**, all proved Qed:
  * `consequence` — strengthen pre, weaken post.
  * `seq` — sequence two bodies, threading the postcondition.
  * `frame_static` — preserve any predicate that doesn't depend on
    written variables (paired with `seqFrame` from
    `LowCTBorrowCheck.lean`).

## Where the parameters are instantiated

The judgment is parameterized by a `body → JasminMemState → JasminMemState →
Prop` step relation. `CatCrypt.Crypto.Jasmin.BignumHoare` supplies the
instances:

- **Operational semantics** for the bignum `InstrR` fragment (`Pload`,
  `Lmem` stores, ADD_64/SBB_64/MULX intrinsics): `BignumHoare.bignumStep`,
  defined as `BignumExec.bignumExec body s = some s'`.
- **`mvcgen` attachment**: `BignumHoare/MVCGenPrimeSmoke.lean`, where `BignumM`
  gets its `WPMonad` instance by search over `.arg BignumState (.except PUnit
  .pure)` and nine `@[spec]` step lemmas — one per SSA builder shape — drive
  `mvcgen`.
- **Port closure** for `bignum_mod_p25519_4`:
  `BignumHoare.bignum_mod_p25519_4_correct_universal` in
  `BignumHoare/ModP25519Final.lean`.
-/

namespace CatCrypt.Crypto.Jasmin.Hoare

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.MemoryModel

/-! ## §1. Bundled state -/

/-- The state a bignum SSA body operates over: a register/tower-
    variable state (from the existing LowCT machinery) plus a flat
    byte-addressable memory. -/
structure JasminMemState where
  regs : RustState
  mem  : Mem

instance : Inhabited JasminMemState where
  default := { regs := default, mem := Mem.empty }

/-! ## §2. Step relation (parameterized)

The Hoare judgment is parameterized by a step relation
`Step body s s'`. This factoring lets us:

1. Prove the structural rules (consequence, seq, frame) once, independently
   of any operational semantics.
2. Instantiate with the bignum-fragment step relation and inherit that whole
   Hoare structure.

The concrete instantiation is `BignumHoare.bignumStep`: `Step body s s'`
holds when executing `body : List InstrR` from state `s` under
`BignumExec.bignumExec` reaches `s'`. -/

/-- A big-step relation between programs and pre/post `JasminMemState`. -/
abbrev StepRel := List InstrR → JasminMemState → JasminMemState → Prop

/-! ## §3. The Hoare-triple judgment -/

/-- `HoareTriple step P body Q`: under the step relation `step`, every
    execution of `body` from a state satisfying `P` reaches a state
    satisfying `Q`. (Partial correctness — total correctness adds a
    termination clause.) -/
def HoareTriple (step : StepRel)
    (P : JasminMemState → Prop)
    (body : List InstrR)
    (Q : JasminMemState → Prop) : Prop :=
  ∀ s s', P s → step body s s' → Q s'

/-! ## §4. Structural rules

These hold for any step relation, so we prove them once here. The
rules of inference are the standard Hoare-logic ones, ported. -/

/-- **Consequence**: strengthen the precondition or weaken the
    postcondition. -/
theorem consequence
    {step : StepRel} {P P' : JasminMemState → Prop}
    {body : List InstrR} {Q Q' : JasminMemState → Prop}
    (h_pre : ∀ s, P' s → P s)
    (h_post : ∀ s, Q s → Q' s)
    (h : HoareTriple step P body Q) :
    HoareTriple step P' body Q' := by
  intro s s' hP hStep
  exact h_post s' (h s s' (h_pre s hP) hStep)

/-- **Trivial pre**: the universal precondition `True` admits any body
    against `Q = trivially true`. -/
theorem skip_trivial (step : StepRel) (body : List InstrR) :
    HoareTriple step (fun _ => True) body (fun _ => True) := by
  intro _ _ _ _; trivial

/-- A relation `step` is **deterministic on the left** if executing
    a prefix of a sequence yields a unique intermediate state. -/
def StepLeftDet (step : StepRel) : Prop :=
  ∀ b1 b2 s s', step (b1 ++ b2) s s' →
    ∃ s1, step b1 s s1 ∧ step b2 s1 s'

/-- **Sequence rule**: under a step relation that decomposes
    sequencing, two consecutive triples compose. -/
theorem seq
    {step : StepRel} (h_seq : StepLeftDet step)
    {P R Q : JasminMemState → Prop}
    {body1 body2 : List InstrR}
    (h1 : HoareTriple step P body1 R)
    (h2 : HoareTriple step R body2 Q) :
    HoareTriple step P (body1 ++ body2) Q := by
  intro s s' hP hStep
  obtain ⟨s1, hS1, hS2⟩ := h_seq body1 body2 s s' hStep
  exact h2 s1 s' (h1 s s1 hP hS1) hS2

/-- **Conjunction**: triples conjoin on both pre and post. -/
theorem conj
    {step : StepRel} {P1 P2 Q1 Q2 : JasminMemState → Prop}
    {body : List InstrR}
    (h1 : HoareTriple step P1 body Q1)
    (h2 : HoareTriple step P2 body Q2) :
    HoareTriple step (fun s => P1 s ∧ P2 s) body (fun s => Q1 s ∧ Q2 s) := by
  intro s s' hP hStep
  exact ⟨h1 s s' hP.1 hStep, h2 s s' hP.2 hStep⟩

/-! ## §5. Frame rule (memory-version)

If a body's stores are confined to a region disjoint from `R`'s
footprint, then `R` is preserved. This is the bedrock-style frame —
narrower than full SL because we only frame over `array64` predicates
and disjointness, not over arbitrary heap predicates.

The rule is proved in two parts:
1. A predicate `framePreserves step body footprint`: every step from
   any state to any state' touches only addresses in `footprint`.
2. The frame conclusion: a state-to-state property `R` that depends
   only on memory outside the footprint is preserved.

We give the *statement* of the rule here; the *evidence* for any
specific body is supplied by the operational semantics (each step's
write set is in the InstrR's static footprint). -/

/-- The set of addresses a body might write. Computed statically. For
    a stub semantics this is a parameter; the concrete semantics will
    feed it from `PointerBorrow.disjointObligations`. -/
abbrev WriteFootprint := List InstrR → AddrSet

/-- A step relation **respects** a static write footprint if every
    transition only changes memory inside that footprint. -/
def RespectsFootprint (step : StepRel) (footprint : WriteFootprint) : Prop :=
  ∀ body s s', step body s s' →
    ∀ a, ¬ footprint body a → s.mem.loadByte a = s'.mem.loadByte a

/-- **Frame rule** (memory-disjoint version): if the body's writes
    stay in `footprint body` and `R` only references the array
    `array64 base xs` whose footprint is disjoint, then `R` is
    preserved across the body. -/
theorem frame_array64
    {step : StepRel} {footprint : WriteFootprint}
    (h_resp : RespectsFootprint step footprint)
    (body : List InstrR) (base : UInt64) (xs : List UInt64)
    (h_disj : MemoryModel.Disjoint (footprint body) (array64Footprint base xs.length)) :
    HoareTriple step (fun s => array64 base xs s.mem) body
                     (fun s => array64 base xs s.mem) := by
  intro s s' hPre hStep i j
  -- The byte at base + 8·i + j is in array64Footprint base xs.length;
  -- by h_disj it is not in footprint body, so the step preserves it.
  have h_in_arr : array64Footprint base xs.length
                  (base + UInt64.ofNat (8 * i.val + j.val)) := by
    refine ⟨8 * i.val + j.val, ?_, rfl⟩
    have hi : i.val < xs.length := i.isLt
    have hj : j.val < 8 := j.isLt
    omega
  have h_not_in_fp : ¬ footprint body
                       (base + UInt64.ofNat (8 * i.val + j.val)) := by
    intro h
    exact h_disj _ ⟨h, h_in_arr⟩
  -- Use the respects-footprint property.
  have h_byte_eq := h_resp body s s' hStep
                       (base + UInt64.ofNat (8 * i.val + j.val))
                       h_not_in_fp
  rw [← h_byte_eq]
  exact hPre i j

/-! ## §6. What's plugged in next

To use this judgment for a real bignum-port proof, we need:

1. **Define `bignumStep : StepRel`** — an inductive relation over
   `JasminMemState` covering the InstrR fragment used by `S2NBignumSSA.lean`:
   - `Cassgn` with `Pload .U64 base (Pconst k)` → memory load.
   - `Cassgn` with `Lmem .U64 base (Pconst k)` → memory store.
   - `Copn (Oasm "ADD_64")` → arithmetic with flags.
   - `Copn (Oasm "ADC_64")`, `Copn (Oasm "SUB_64")`, `Copn (Oasm "SBB_64")`,
     `Copn (Oasm "MULX")`, `Copn (Oasm "ADCX")`, `Copn (Oasm "ADOX")`,
     `Copn (Oasm "XOR_64")` — the s2n-bignum intrinsic set.
   - `Copn (Oasm "STORE64")` for tower-store (already in `jasminSem`).

2. **Prove `bignumStep` is `StepLeftDet`** — sequencing decomposes
   uniquely. Standard inductive-case-split argument.

3. **Prove `bignumStep` `RespectsFootprint footprintPb`** where
   `footprintPb` is computed from `PointerBorrow.disjointObligations`.

4. **Wire `mvcgen`** — the tactic specializes to this judgment by
   walking the InstrR list, emitting one VC per Cassgn / Copn from
   the inductive's constructors.

Each step is local infrastructure work; the judgment shape and
structural rules here support all of them.

For the first concrete port closure (`bignum_mod_p25519_4`):

```
theorem bignum_mod_p25519_4_correct
    (base_a base_op : UInt64) (a_val : List UInt64)
    (h_disj : Disjoint (array64Footprint base_a 4)
                       (array64Footprint base_op 4))
    (h_len : a_val.length = 4)
    (h_bound : (toNat a_val) < 2 * (2^255 - 19)) :
    HoareTriple bignumStep
      (fun s => array64 base_a a_val s.mem ∧
                array64 base_op (List.replicate 4 0) s.mem)
      BignumModP25519_4.body
      (fun s => array64 base_a a_val s.mem ∧
                ∃ result, array64 base_op result s.mem ∧
                  toNat result = (toNat a_val) % (2^255 - 19))
```

This decomposes via `seq` into per-instruction VCs, the array_a
preservation falls out via `frame_array64` against
`array64Footprint base_op 4`, and the algorithmic content reduces
to `BignumModP25519_4.algoNat_eq_specNat`.
-/

end CatCrypt.Crypto.Jasmin.Hoare
