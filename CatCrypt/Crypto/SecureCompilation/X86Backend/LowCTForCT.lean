/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT

/-!
# Source→machine compiler, Phase 3: the literal-bound `RFor` loop by unrolling

This module extends the verified scalar basic-block compiler
(`LowCTToJInstrCT.lean`) to **bounded control flow**: the literal-bound
source for-loop `LowCT.RFor x n body`, where `n` is a closed compile-time
`Nat`.

## Why unrolling, and why CT is trivial here

The machine instruction subset (`JInstr`, `runBlock`) is **straight-line** —
there is no machine branch.  A literal-bound loop is therefore lowered by
**unrolling**: iteration `i` emits `mov ρx, imm i` (set the loop variable to
the literal index `i`) followed by the lowering of the body, and the `n`
iteration blocks are concatenated for `i = 0 … n-1`.

Two consequences, both stated honestly:

* **No emitted branch.**  The unrolled block is one straight-line sequence of
  the same `mov`/`add`/`and`/`xor`/`imul` instructions the scalar block
  compiler already emits — plus a `mov ρx, imm i` per iteration, which is a
  register write with an immediate operand (no memory operand at all).  So the
  whole block is `allDirect`, and machine constant-time follows from the
  keystone `allDirect_constant_time` exactly as in the straight-line case.

* **No secret-dependent control flow.**  The loop bound `n` is a literal, and
  the per-iteration loop-variable value `i` is a literal — neither depends on
  any (possibly secret) runtime value.  This is exactly the schedule
  constant-time crypto uses: bounded loops with public, statically-known trip
  counts, unrolled (or compiled to a counted loop with a public counter) so
  that no branch is taken on a secret.

General non-termination / data-dependent loop bounds are **out of scope** —
the agreed scope is terminating, statically-bounded crypto loops, which is
what `RFor` models and what constant-time code is restricted to.

## What is proved

* `ForSrc` — a faithful capture of the bounded loop `{ x, n, body }` whose
  body is a `List ArithSrc` (the scalar fragment the reused block compiler
  handles), with `ForSrc.toLowCT` embedding it into the **real**
  `LowCT.RFor x n (body-as-RSeq)` (reusing `ArithSrc.seqToLowCT`).
* `lowerFor` — the unrolling lowering.
* `forDenote` — the source iteration fold, matched arm-for-arm to the real
  `RustExec` `forZero`/`forSucc` operational semantics (see `forDenote_succ`
  and `forDenote_rustExec`).
* `lowerFor_allDirect` / `lowerFor_constant_time` — machine constant-time
  (the easy genuine half: the unrolled block is all `IsDirect`).
* `lowerFor_denote` — denote preservation: the unrolled machine block tracks
  `forDenote` under register-allocation well-formedness, proved by induction
  on `n` using `runBlock_append` per iteration and `lowerSeq_denote` for each
  body copy.
* `forDenote_rustExec` / `lowerFor_denote_rustExec` — the tie to the genuine
  `RustExec.RFor` operational semantics: `forDenote` *is* the post-state the
  real `RForᵢ` arms reach, so the machine run tracks the real source loop.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTForCT

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT
open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. The bounded-loop source fragment -/

/-- A literal-bound for-loop over the scalar-arith fragment: run `body` (a
    straight-line `List ArithSrc`) `n` times, with the scalar loop variable
    `x` set to `0, 1, …, n-1` on successive iterations.  `n` is a closed
    compile-time `Nat`.  This is a faithful subset of `LowCT.RFor x n …`. -/
structure ForSrc where
  x    : String
  n    : Nat
  body : List ArithSrc

/-! ## 2. Embedding into real `LowCT` -/

/-- **The embedding into real `LowCT`.**  A `ForSrc` is the genuine
    `LowCT.RFor x n B` command, where the body `B` is the right-nested
    `RSeq` chain of `RScalarSetExpr` nodes built by `ArithSrc.seqToLowCT`
    (the same embedding the basic-block compiler uses).  This makes the loop
    a real `LowCT` node, executed by the genuine `RustExec.forZero`/`forSucc`
    semantics — not a disconnected re-statement. -/
def ForSrc.toLowCT (f : ForSrc) : LowCT :=
  .RFor f.x f.n (ArithSrc.seqToLowCT f.body)

/-! ## 3. The loop-variable immediate set: `mov ρx, imm i` -/

/-- Set the machine register `r` to the literal index `i`.  Lowers the
    source loop-variable update `x := i` (where `i` is a compile-time literal,
    not a runtime value).  This is `Ox86_MOV_instr` with an immediate operand
    — a register write, no memory operand. -/
def movImm (r : String) (i : Nat) : JInstr 64 :=
  .mov r (.imm i)

/-- `movImm` is `IsDirect`: it is a `mov` with an immediate source, so it
    has no memory operand (the only `¬ IsDirect` opcodes are
    `loadMemIdx`/`storeMemIdx`). -/
@[simp] theorem movImm_isDirect (r : String) (i : Nat) :
    decide (IsDirect (movImm r i)) = true := rfl

/-- `movImm r i` writes `BitVec.ofNat 64 i` to register `r`. -/
theorem evalInstr_movImm (r : String) (i : Nat) (s : JState 64) :
    evalInstr s (movImm r i) = s.setReg r (BitVec.ofNat 64 i) := by
  simp [movImm, evalInstr, x86_MOV, JOperand.eval]

/-- **State match after a loop-variable immediate set.**  If `js` matches `rs`
    under `ρ`, then after `mov (ρ x) (imm i)` the machine state matches the
    source state `rsSetScalar rs x i` — the machine register `ρ x` now holds
    `BitVec.ofNat 64 i`, exactly the truncation of the new source scalar `i`,
    and (by injectivity) every other register is undisturbed, matching the
    untouched source slots. -/
theorem movImm_stateMatch (ρ : RegMap) (hρ : Function.Injective ρ)
    (x : String) (i : Nat) (rs : RustState) (js : JState 64)
    (hmatch : StateMatch ρ rs js) :
    StateMatch ρ (rsSetScalar rs x i) (evalInstr js (movImm (ρ x) i)) := by
  intro v
  rw [evalInstr_movImm]
  by_cases hv : v = x
  · subst hv
    rw [JState.get_setReg_same]
    simp [rsSetScalar]
  · have hvx : ρ v ≠ ρ x := fun h => hv (hρ h)
    rw [JState.get_setReg_other _ _ _ _ hvx]
    simp only [rsSetScalar, beq_eq_false_iff_ne.mpr hv, Bool.false_eq_true, if_false]
    exact hmatch v

/-! ## 4. The unrolling lowering -/

/-- The single-iteration block for index `i`: set the loop variable to the
    literal `i`, then run the lowered body. -/
def lowerForIter (ρ : RegMap) (f : ForSrc) (i : Nat) : List (JInstr 64) :=
  movImm (ρ f.x) i :: lowerSeq ρ f.body

/-- **The unrolling lowering.**  Concatenate the per-iteration blocks for
    `i = 0 … n-1`.  Straight-line: no machine branch is emitted. -/
def lowerFor (ρ : RegMap) (f : ForSrc) : List (JInstr 64) :=
  (List.range f.n).flatMap (lowerForIter ρ f)

/-! ## 5. The source iteration fold (matched to `RustExec`) -/

/-- **The source-side loop semantics.**  Fold the per-iteration update
    `rs ↦ srcDenote body (rsSetScalar rs x i)` over `i = 0 … n-1`.  This is
    exactly the post-state the real `RustExec` `forZero`/`forSucc` arms reach:
    each iteration first sets the scalar `x := i` (`rsSetScalar`) then runs the
    body (`srcDenote`), in index order `0, 1, …, n-1` — see `forDenote_succ`
    and `forDenote_rustExec`. -/
def forDenote (f : ForSrc) (rs : RustState) : RustState :=
  (List.range f.n).foldl
    (fun rs i => srcDenote f.body (rsSetScalar rs f.x i)) rs

/-- The fold over a `ForSrc` with `n = 0` iterations is the identity — matches
    `RustExec.forZero`. -/
@[simp] theorem forDenote_zero (x : String) (body : List ArithSrc) (rs : RustState) :
    forDenote ⟨x, 0, body⟩ rs = rs := rfl

/-- The fold over `n+1` iterations runs the first `n` iterations, then sets
    `x := n` and runs the body once more — matches `RustExec.forSucc`. -/
theorem forDenote_succ (x : String) (n : Nat) (body : List ArithSrc) (rs : RustState) :
    forDenote ⟨x, n + 1, body⟩ rs =
      srcDenote body (rsSetScalar (forDenote ⟨x, n, body⟩ rs) x n) := by
  simp only [forDenote, List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil]

/-! ## 6. Machine constant-time: the easy genuine half -/

/-- `lowerForIter` is `allDirect`: a `movImm` (direct) followed by the lowered
    body (direct by `lowerSeq_allDirect`). -/
theorem lowerForIter_allDirect (ρ : RegMap) (f : ForSrc) (i : Nat) :
    allDirect (lowerForIter ρ f i) = true := by
  rw [lowerForIter, allDirect, List.all_cons, movImm_isDirect, Bool.true_and]
  exact lowerSeq_allDirect ρ f.body

/-- **Machine constant-time (the unrolled block is all `IsDirect`).**  Every
    instruction of the unrolled loop is direct: each iteration is a `movImm`
    (immediate register write) plus the memory-free scalar-arith body.  No
    `loadMemIdx`/`storeMemIdx`, and no branch. -/
theorem lowerFor_allDirect (ρ : RegMap) (f : ForSrc) :
    allDirect (lowerFor ρ f) = true := by
  rw [lowerFor, allDirect, List.all_eq_true]
  intro i hi
  rw [List.mem_flatMap] at hi
  obtain ⟨k, _, hk⟩ := hi
  have := allDirect_mem_isDirect _ (lowerForIter_allDirect ρ f k) i hk
  exact decide_eq_true this

/-- **Source→machine constant-time, bounded-loop level.**  The unrolling of any
    literal-bound scalar-arith for-loop produces the **same** machine leakage
    trace from any two initial states: the loop bound and per-iteration index
    are literals, so the observable control-flow + memory-address sequence is a
    function of the program text alone.  This is the bounded-loop instance of
    the machine keystone — bounded loop ⇒ straight-line ⇒ constant-time, no
    secret-dependent branch. -/
theorem lowerFor_constant_time (ρ : RegMap) (f : ForSrc) (s₁ s₂ : JState 64) :
    blockLeak s₁ (lowerFor ρ f) = blockLeak s₂ (lowerFor ρ f) :=
  allDirect_constant_time (lowerFor ρ f) (lowerFor_allDirect ρ f) s₁ s₂

/-! ## 7. Denote preservation: the hard half

`lowerFor_denote`: under the register map `ρ` (injective) and the body
well-formedness condition (each `ArithSrc` in the body has `b ≠ dst`, the
same condition `lowerSeq_denote` consumes), the unrolled machine block tracks
the source iteration fold `forDenote`.  Proved by induction on `n`, splitting
the unrolled block per iteration with `runBlock_append`, threading
`StateMatch` through the loop-variable set (`movImm_stateMatch`) and the body
(`lowerSeq_denote`). -/

/-- One unrolled iteration tracks one source iteration: from a matching state,
    running `movImm (ρ x) i :: lowerSeq ρ body` ends in a state matching
    `srcDenote body (rsSetScalar rs x i)`. -/
theorem lowerForIter_denote (ρ : RegMap) (hρ : Function.Injective ρ)
    (f : ForSrc) (hwf : ∀ p ∈ f.body, p.b ≠ p.dst)
    (i : Nat) (rs : RustState) (js : JState 64) (hmatch : StateMatch ρ rs js) :
    StateMatch ρ (srcDenote f.body (rsSetScalar rs f.x i))
      (runBlock js (lowerForIter ρ f i)) := by
  rw [lowerForIter, runBlock_cons]
  exact lowerSeq_denote ρ hρ f.body hwf _ _
    (movImm_stateMatch ρ hρ f.x i rs js hmatch)

/-- **Denote preservation (the hard half).**  If the machine state `js`
    matches the source state `rs` under `ρ`, then after running the unrolled
    loop the machine state matches the source post-state `forDenote f rs`
    — the genuine `RustExec.RFor` result (see `lowerFor_denote_rustExec`).

    Hypotheses are the register-allocation well-formedness conditions:
    * `ρ` injective — distinct source slots get distinct machine registers
      (so the loop-variable set `mov ρx` does not disturb the image of any
      other slot);
    * each body statement `p` has `p.b ≠ p.dst` — the per-statement condition
      the reused `lowerSeq_denote` consumes.

    Proven by induction on `f.n`, peeling one iteration at a time with
    `runBlock_append` (the unrolled block splits as
    `iterations 0..n-1 ++ iteration n`) and matching it to `forDenote_succ`. -/
theorem lowerFor_denote (ρ : RegMap) (hρ : Function.Injective ρ) (f : ForSrc)
    (hwf : ∀ p ∈ f.body, p.b ≠ p.dst)
    (rs : RustState) (js : JState 64) (hmatch : StateMatch ρ rs js) :
    StateMatch ρ (forDenote f rs) (runBlock js (lowerFor ρ f)) := by
  obtain ⟨x, n, body⟩ := f
  have hwf' : ∀ p ∈ body, p.b ≠ p.dst := hwf
  clear hwf
  induction n generalizing rs js with
  | zero => simpa [lowerFor, forDenote] using hmatch
  | succ k ih =>
    -- Unrolled block: iterations 0..k-1, then iteration k.  `lowerForIter`
    -- depends only on `x`/`body`, so the per-iteration block is the same for
    -- the `k+1` and `k` structures.
    have hiter : lowerForIter ρ ⟨x, k + 1, body⟩ = lowerForIter ρ ⟨x, k, body⟩ := rfl
    have hsplit : lowerFor ρ ⟨x, k + 1, body⟩ =
        lowerFor ρ ⟨x, k, body⟩ ++ lowerForIter ρ ⟨x, k, body⟩ k := by
      simp only [lowerFor, List.range_succ, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, hiter]
    rw [hsplit, runBlock_append, forDenote_succ]
    -- IH: the first k iterations track forDenote ⟨x, k, body⟩.
    have hk : StateMatch ρ (forDenote ⟨x, k, body⟩ rs)
        (runBlock js (lowerFor ρ ⟨x, k, body⟩)) :=
      ih rs js hmatch
    -- One more iteration (index k) tracks the final source iteration.
    exact lowerForIter_denote ρ hρ ⟨x, k, body⟩ hwf' k _ _ hk

/-! ## 8. The tie to the genuine `RustExec.RFor` operational semantics

`forDenote` is not a re-stated denotation: it is provably the post-state the
real `RustExec` `forZero`/`forSucc` arms reach on `f.toLowCT`.  So the
machine-run correspondence `lowerFor_denote` is a correspondence against the
genuine source loop semantics. -/

/-- One source iteration of the real `RustExec` over the body chain
    `ArithSrc.seqToLowCT body`: from state `rs`, `RustExec` steps the body to
    `srcDenote body rs`.  This is `lowerSeq`'s source-semantics tie, lifted to
    the `RSeq` chain.  Proved by induction on the body using `RustExec.seq`
    and the per-statement `ArithSrc.rustExec`. -/
theorem seqToLowCT_rustExec (N : Nat) (leafSpec : LeafSpec)
    (body : List ArithSrc) (rs : RustState) :
    RustExec N leafSpec (ArithSrc.seqToLowCT body) rs (srcDenote body rs) := by
  induction body generalizing rs with
  | nil => simpa [ArithSrc.seqToLowCT, srcDenote] using RustExec.skip rs
  | cons p ps ih =>
    rw [ArithSrc.seqToLowCT_cons, srcDenote_cons]
    exact RustExec.seq _ _ _ _ _ (ArithSrc.rustExec N leafSpec p rs) (ih _)

/-- **`forDenote` is the genuine `RustExec.RFor` post-state.**  Running the real
    operational semantics on `f.toLowCT = RFor x n (body-chain)` from `rs`
    reaches exactly `forDenote f rs`.  Proved by induction on `f.n` matching
    `forZero` (`forDenote_zero`) and `forSucc` (`forDenote_succ`), with each
    body iteration discharged by `seqToLowCT_rustExec`. -/
theorem forDenote_rustExec (N : Nat) (leafSpec : LeafSpec) (f : ForSrc)
    (rs : RustState) :
    RustExec N leafSpec f.toLowCT rs (forDenote f rs) := by
  obtain ⟨x, n, body⟩ := f
  induction n generalizing rs with
  | zero =>
    simpa [ForSrc.toLowCT, forDenote_zero] using RustExec.forZero x (ArithSrc.seqToLowCT body) rs
  | succ k ih =>
    rw [ForSrc.toLowCT, forDenote_succ]
    refine RustExec.forSucc x k (ArithSrc.seqToLowCT body) rs
      (forDenote ⟨x, k, body⟩ rs) _ ?_ ?_
    · exact ih rs
    · exact seqToLowCT_rustExec N leafSpec body _

/-- **Determinism of `RustExec` on the body chain.**  The body is built only
    from `RSkip`/`RSeq`/`RScalarSetExpr` (the `ArithSrc.seqToLowCT` shape),
    each of which has a single deterministic `RustExec` arm, so the post-state
    is forced to `srcDenote body rs`. -/
theorem seqToLowCT_rustExec_det (N : Nat) (leafSpec : LeafSpec)
    (body : List ArithSrc) (rs rs' : RustState)
    (h : RustExec N leafSpec (ArithSrc.seqToLowCT body) rs rs') :
    rs' = srcDenote body rs := by
  induction body generalizing rs rs' with
  | nil =>
    rw [ArithSrc.seqToLowCT_nil] at h
    cases h
    rfl
  | cons p ps ih =>
    rw [ArithSrc.seqToLowCT_cons] at h
    cases h with
    | seq _ _ _ r1 _ hhead htail =>
      -- `p.toLowCT` is a single `RScalarSetExpr`; invert it.
      rw [ArithSrc.toLowCT] at hhead
      cases hhead
      rw [srcDenote_cons]
      exact ih _ _ htail

/-- **Determinism of `RustExec` on the bounded loop `f.toLowCT`.**  By induction
    on `f.n`, inverting `forZero`/`forSucc` and using `seqToLowCT_rustExec_det`
    for each body iteration, the post-state is forced to `forDenote f rs`. -/
theorem rustExec_RFor_det (N : Nat) (leafSpec : LeafSpec) (f : ForSrc)
    (rs rs' : RustState)
    (h : RustExec N leafSpec f.toLowCT rs rs') :
    rs' = forDenote f rs := by
  obtain ⟨x, n, body⟩ := f
  induction n generalizing rs rs' with
  | zero =>
    rw [ForSrc.toLowCT] at h
    cases h
    rfl
  | succ k ih =>
    rw [ForSrc.toLowCT] at h
    cases h with
    | forSucc _ _ _ _ r1 _ hInner hBody =>
      have hr1 : r1 = forDenote ⟨x, k, body⟩ rs := ih rs r1 hInner
      subst hr1
      rw [forDenote_succ]
      exact seqToLowCT_rustExec_det N leafSpec body _ _ hBody

/-- **Denote preservation, against the real `RustExec` (end to end).**  For the
    unique source post-state `rs'` reached by the genuine `RustExec` on the
    bounded loop `f.toLowCT`, the machine run of the unrolling ends in a
    `StateMatch`-related state.  Combines `forDenote_rustExec` (the source loop
    *is* `forDenote`, via determinism of `RustExec` on `RFor`) with
    `lowerFor_denote`.  This is the bounded-loop source-operational-semantics
    ⇒ machine-run correspondence. -/
theorem lowerFor_denote_rustExec (N : Nat) (leafSpec : LeafSpec)
    (ρ : RegMap) (hρ : Function.Injective ρ) (f : ForSrc)
    (hwf : ∀ p ∈ f.body, p.b ≠ p.dst)
    (rs rs' : RustState) (js : JState 64) (hmatch : StateMatch ρ rs js)
    (hexec : RustExec N leafSpec f.toLowCT rs rs') :
    StateMatch ρ rs' (runBlock js (lowerFor ρ f)) := by
  -- `RustExec` on a `RFor x n (body-chain)` is deterministic in the body
  -- (each iteration is a deterministic scalar-set chain), so `rs'` is exactly
  -- `forDenote f rs`.  We obtain that equality by running the determined
  -- `forDenote_rustExec` derivation and the RFor determinism rule.
  have hdet : rs' = forDenote f rs :=
    rustExec_RFor_det N leafSpec f rs rs' hexec
  rw [hdet]
  exact lowerFor_denote ρ hρ f hwf rs js hmatch

end CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTForCT
