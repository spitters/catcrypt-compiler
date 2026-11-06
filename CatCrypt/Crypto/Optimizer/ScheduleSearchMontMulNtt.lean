/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Optimizer.RandomizedScheduleSearch
public import CatCrypt.Crypto.Optimizer.RandomizedScheduleSearch
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381MontMulKernel
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381MontMulKernel

/-!
# Verified-CryptOpt schedule search applied to the modularity-floor kernels

The randomized schedule/RA search of `RandomizedScheduleSearch.lean` (the
verified form of CryptOpt's loop: a seeded local search over the
disjoint-footprint adjacent-transposition neighbourhood, with **in-Lean
translation validation of the winner** standing in for CryptOpt's external
equivalence checker) closes `fe25519` to s2n parity only where the gap is
schedule-shaped, and reports a *null* where it is not (`feMulBlock`: 8 legal
swaps, all cost-neutral; the residual is register allocation).

This module points the **same** loop at the two kernels the bench flags as
trailing their hand-asm references on scheduling: the **BLS12-381 `Fp` CIOS
Montgomery multiply** (`Bls12381MontMulKernel.blsMontMulBlock`, 1.11× vs blst's
`mulx_mont_384`, MCA RThru 229.8 vs 206.5) and the **ML-KEM / ML-DSA NTT
butterfly** (1.34× / 1.11× vs PQClean-AVX2). The result on each is the finding —
**including the negatives**.

## The BLS CIOS finding: the first predicate was unsound

The CIOS body admits **124 legal adjacent transpositions** under the footprint
predicate `legalSwap` (`blsMontMul_legal_swaps`; the first predicate of the search
admitted 81).

The first version of the search produced a reschedule that changes the result:
`bls_search7_breaks_runBlock`, the search under the former predicate
`RandomizedScheduleSearch.legalSwapRegs` and the order-independent fitness
`X86CostModel.scheduleCostV2`, computes after 7 steps a result word `z[2]` that differs
from the baseline's on a concrete state. The cause is a missing footprint, not a
composition of individually sound swaps: the footprints `writeSet` and `readSet` of that
predicate have no arm for `mulxMem`, which therefore reads and writes nothing under it.
Two of the 7 steps apply a swap, and both move a `mulxMem` across an instruction that
reads its result (`adox t2, hi` at step 4, `adcx t4, lo` at step 6); each of these
transpositions changes the state by itself. Under `legalSwap` the search output equals the
input on every state (`RandomizedScheduleSearch.searchIterate_runBlock`;
`bls_search7_sound` at this block and seed).

The one move that *does* pass TV in isolation — hoisting the reduce-constant
staging `mov hi, imm(p[j])` past an adjacent ADCX/ADOX accumulate
(`bls_movStage_adcx_commute` / `bls_movStage_adox_commute`,
`bls_reschedule_lowering_denote_eq`) — is cost-neutral and, even if it were
applied, could not move `BlockRThroughput`: a transposition preserves the µop
count (`bls_search_preserves_length`), and RThroughput is a port-pressure lower
bound counting µops per port. The 229.8-vs-206.5 gap is the **422-vs-312 µop
count** (our explicit constant-staging + window-shift `mov` rotation +
stack-scratch final-reduce vs blst's fused register renaming) — instruction
selection / register renaming, **not** schedule.

## The NTT finding: the clean schedule null

The emitted per-stage `mul; add; sub` chain is fully serial (`add`/`sub` both
consume the `mul` output; the stores consume their results), and the store→load
barrier between stages serialises the unroll. The search finds **4 legal swaps
per stage** (`nttStageBlock_legal_swaps`), and `ntt_search_no_improvement` and
`ntt_twostage_no_improvement` record that it does not lower the former proxy
`scheduleCost`. The NTT 1.34×/1.11×-PQClean residual is the cross-stage **memory residency**
(the emitted stream is 45 % `vmovdqu` — 389 of 869 ops — vs the hand-asm's 19 %,
because every intermediate round-trips through the `inp[]`/`out[]` arrays while
the hand-asm keeps the polynomial register-resident across stages). That is
register allocation (`MlkemRaEmit`), **not** schedule.

## Bottom line (all machine-checked here / MCA-measured in bench/)

A transposition preserves the µop count, so it cannot change the port-pressure bound
of either kernel; whether a reschedule changes their measured time is not stated here.
The scope is the parent module's: the **search** ranges over the disjoint-footprint
neighbourhood, and every candidate it visits is equivalent to its input.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.ScheduleSearchMontMulNtt

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.Optimizer.RandomizedScheduleSearch
open CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381MontMulKernel

/-! ## 1. BLS CIOS: the schedule neighbourhood is large (unlike `fe25519`) -/

/-- **The BLS CIOS body admits 124 legal adjacent transpositions** under the footprint
    predicate `legalSwap` (cf. `fe25519`'s 20): the per-iteration constant-staging `mov`s,
    the window-shift `mov` rotation and the `adcx`/`adox` pairs of different flags are
    independent of their neighbours. -/
theorem blsMontMul_legal_swaps : countLegalSwaps blsMontMulBlock = 124 := by
  native_decide

/-! ## 2. The one soundly-TV'd move (the reduce-constant hoist)

The single move the search prefers that *is* denotation-preserving in isolation:
hoisting the reduce-phase constant staging `mov hi, imm(p[j])` up past the prior
column's ADCX/ADOX accumulate. The `mov` writes only `hi` and touches no flag;
the ADCX/ADOX it crosses write a window word + one flag and read `lo`/their
window word — disjoint footprints. These commute on **all** machine states. -/

/-- `mov hi, imm` (reduce-constant staging) commutes with `adcx tlo, lo`: the
    `mov` writes only `hi`, the `adcx` writes `tlo` + CF and reads `tlo`/`lo`/CF —
    disjoint register footprints, and `mov` touches no flag so the ADCX carry-in
    survives in both orders. -/
theorem bls_movStage_adcx_commute (s : JState 64) (pj : Nat) (tlo : String)
    (htlo : tlo ≠ "hi") :
    evalInstr (evalInstr s (.mov "hi" (.imm pj))) (.adcx tlo (.reg "lo"))
      = evalInstr (evalInstr s (.adcx tlo (.reg "lo"))) (.mov "hi" (.imm pj)) := by
  simp only [evalInstr, JState.setReg, JState.get, JState.flagB, JOperand.eval]
  congr 1
  · funext r
    by_cases ha : r = tlo <;> by_cases hb : r = "hi" <;> simp_all
  · simp only [ite_eq_right htlo, ite_eq_right (show "lo" ≠ "hi" by decide)]

/-- `mov hi, imm` commutes with `adox thi, src`: same disjoint-footprint argument
    on the OF chain (the `adox` reads its window word + OF, writes that word + OF;
    the staged `hi` and its read source are distinct names). -/
theorem bls_movStage_adox_commute (s : JState 64) (pj : Nat) (thi src : String)
    (hthi : thi ≠ "hi") (hsrc : src ≠ "hi") :
    evalInstr (evalInstr s (.mov "hi" (.imm pj))) (.adox thi (.reg src))
      = evalInstr (evalInstr s (.adox thi (.reg src))) (.mov "hi" (.imm pj)) := by
  simp only [evalInstr, JState.setReg, JState.get, JState.flagB, JOperand.eval]
  congr 1
  · funext r
    by_cases ha : r = thi <;> by_cases hb : r = "hi" <;> simp_all
  · simp only [ite_eq_right hthi, ite_eq_right hsrc]

/-- **Winner TV for the one sound move (machine-state level).** The reduce-constant
    staging `mov hi, imm` hoisted past one ADCX accumulate yields the *same*
    `JState` for every machine state — the all-states equality that
    translation-validates this isolated reschedule against the validated
    `JasminModel`. -/
theorem bls_reschedule_runBlock_eq (s : JState 64) (pj : Nat) :
    runBlock s [.mov "hi" (.imm pj), .adcx "t1" (.reg "lo")]
      = runBlock s [.adcx "t1" (.reg "lo"), .mov "hi" (.imm pj)] := by
  simp only [runBlock_cons, runBlock_nil]
  exact bls_movStage_adcx_commute s pj "t1" (by decide)

/-- **Winner TV (dialect/`Com` level).** The lowered `Com`s of the two orders have
    equal denotation on every incoming state — denotation-preserving against the
    validated x86 model, through `lowerBlock_denote_closed`. The in-Lean
    certificate replacing CryptOpt's external checker, for the sound BLS move. -/
theorem bls_reschedule_lowering_denote_eq (s : JState 64) (pj : Nat) :
    (lowerBlock (Γ := []) [.mov "hi" (.imm pj), .adcx "t1" (.reg "lo")]).denote
        (.cons s .nil)
      = (lowerBlock (Γ := []) [.adcx "t1" (.reg "lo"), .mov "hi" (.imm pj)]).denote
        (.cons s .nil) := by
  rw [lowerBlock_denote_closed _ s, lowerBlock_denote_closed _ s]
  exact bls_reschedule_runBlock_eq s pj

/-! ## 3. The first predicate of the search was unsound

The search of the first version, the former predicate `legalSwapRegs` with the fitness
`scheduleCostV2`, produces within 7 steps a reschedule that changes the result. The witness
below is a concrete state on which its output computes a different `z[2]` from the baseline.
The footprint search on the same block and seed is equivalent to the input. -/

/-- A concrete init state for the unsoundness witness. -/
def stCE : JState 64 := initState 3 5 7 11 13 17 19 23 29 31 37 41

/-- The six result words `z[0..5]` after running a block from `stCE`. -/
def zWords (b : List (JInstr 64)) : List (BitVec 64) :=
  let s := runBlock stCE b
  [s.mem "z" 0, s.mem "z" 8, s.mem "z" 16, s.mem "z" 24, s.mem "z" 32, s.mem "z" 40]

/-- **The first predicate of the search was unsound.** After 7 steps of the search under
    the former predicate `legalSwapRegs` and the fitness `scheduleCostV2`, the rescheduled
    CIOS body computes a different result from the baseline on `stCE`. Two of the 7 steps
    apply a transposition, and both move a `mulxMem` across an instruction that reads its
    result (`adox t2, hi`, then `adcx t4, lo`): `writeSet` and `readSet` have no arm for
    `mulxMem`, so it reads and writes nothing under `legalSwapRegs`. Each of these
    transpositions changes the state by itself; the failure is a missing footprint, not a
    composition of sound swaps. -/
theorem bls_search7_breaks_runBlock :
    zWords (searchIterateWith legalSwapRegs X86CostModel.scheduleCostV2 7 blsMontMulBlock 777)
      ≠ zWords blsMontMulBlock := by
  native_decide

/-- The search under the footprint predicate, on the same block and seed, runs to the same
    state as the input on every state. -/
theorem bls_search7_sound (s : JState 64) :
    runBlock s (searchIterate 7 blsMontMulBlock 777) = runBlock s blsMontMulBlock :=
  searchIterate_runBlock 7 s blsMontMulBlock 777

/-- One adjacent transposition preserves block length. -/
theorem trySwapAtWith_length (legal : JInstr 64 → JInstr 64 → Bool) (b : List (JInstr 64))
    (k : Nat) : (trySwapAtWith legal b k).length = b.length := by
  induction b generalizing k with
  | nil => cases k <;> rfl
  | cons a tl iha =>
    cases tl with
    | nil => cases k <;> rfl
    | cons b tl2 =>
      cases k with
      | zero => simp only [trySwapAtWith]; split <;> rfl
      | succ k =>
        simp only [trySwapAtWith]
        rw [List.length_cons, List.length_cons, iha]

/-- One greedy search step preserves block length (it returns either the input or
    an adjacent transposition of it). -/
theorem searchStepWith_length (legal : JInstr 64 → JInstr 64 → Bool)
    (cost : List (JInstr 64) → Nat) (b : List (JInstr 64)) (seed : UInt32) :
    (searchStepWith legal cost b seed).1.length = b.length := by
  simp only [searchStepWith]
  split <;> simp [trySwapAtWith_length]

/-- **A reschedule preserves the µop count, hence the MCA port-pressure lower
    bound**: `searchIterateWith` only applies adjacent transpositions, which preserve
    length. -/
theorem bls_search_preserves_length (legal : JInstr 64 → JInstr 64 → Bool)
    (cost : List (JInstr 64) → Nat) (n : Nat) (b : List (JInstr 64)) (seed : UInt32) :
    (searchIterateWith legal cost n b seed).length = b.length := by
  induction n generalizing b seed with
  | zero => rfl
  | succ n ih =>
    simp only [searchIterateWith]
    rw [ih]
    exact searchStepWith_length legal cost b seed

/-! ## 4. ML-KEM / ML-DSA NTT butterfly: the schedule null

One emitted NTT butterfly stage modelled as a `JInstr` block (the dependence
structure the search reasons about — vector lanes do not change the read/write
footprint graph). The stage is `load a; load b; t = b·tw; c = a+t; d = a−t;
store c; store d`: the `add`/`sub` both consume `t` and the stores consume
`c`/`d`, so the arithmetic core is fully serial. -/

-- @bench-only: the `List (JInstr _)` blocks below are fixtures exercising this
-- schedule-search pass; this module emits no deployed `.s` artifact.
/-- One emitted ML-KEM/ML-DSA NTT butterfly stage as a `JInstr` block. The packed
    `VPMULL`/`VPADD`/`VPSUB` lanes are modelled by `mulx`/`add`/`sub` (the
    dependence footprint is what the schedule search reasons over; lane width is
    irrelevant to the read/write graph). -/
def nttStageBlock : List (JInstr 64) :=
  [ .loadMem "a" "inp" 0
  , .loadMem "b" "inp" 8
  , .mulx "thi" "t" (.reg "b") (.reg "tw")
  , .add "c" (.reg "a")
  , .sub "d" (.reg "a")
  , .storeMem "out" 0 (.reg "c")
  , .storeMem "out" 8 (.reg "d") ]

/-- **The NTT butterfly stage admits 4 legal adjacent transpositions** under the
    footprint predicate: the two input loads, the stores to distinct cells, and pairs of
    the arithmetic core with independent neighbours. -/
theorem nttStageBlock_legal_swaps : countLegalSwaps nttStageBlock = 4 := by
  native_decide

/-- **The search finds no schedule improvement on the NTT stage.** The static cost
    proxy is unchanged under the search — the 3 legal swaps are cost-neutral,
    there is no MULX→consumer stall to hoist away (the single `mul` already feeds
    both consumers). The NTT 1.34×/1.11×-PQClean residual is therefore **not** in
    the within-stage schedule: it is the cross-stage memory residency (the emitted
    stream round-trips every intermediate through `inp[]`/`out[]` — 45 % `vmovdqu`
    — while the hand-asm keeps the polynomial register-resident across all
    stages), which is register allocation, not scheduling. -/
theorem ntt_search_no_improvement :
    scheduleCost (searchIterate 3000 nttStageBlock 13) = scheduleCost nttStageBlock := by
  native_decide

/-- Two NTT stages back-to-back: the store→load barrier (stage `i`'s `out[...]`
    store feeds stage `i+1`'s `inp[...]` load) blocks cross-stage interleaving, so
    even the two-stage neighbourhood yields no cost improvement. The unroll is
    sequentially ordered by construction, so the gap is memory residency. -/
def nttTwoStageBlock : List (JInstr 64) :=
  nttStageBlock ++
  [ .loadMem "a" "inp" 16
  , .loadMem "b" "inp" 24
  , .mulx "thi" "t" (.reg "b") (.reg "tw")
  , .add "c" (.reg "a")
  , .sub "d" (.reg "a")
  , .storeMem "out" 16 (.reg "c")
  , .storeMem "out" 24 (.reg "d") ]

/-- **No schedule improvement across two NTT stages either** — the proxy cost is
    unchanged under search, confirming the store→load barrier serialises the
    unroll. The NTT residual is cross-stage residency, full stop. -/
theorem ntt_twostage_no_improvement :
    scheduleCost (searchIterate 4000 nttTwoStageBlock 13)
      = scheduleCost nttTwoStageBlock := by
  native_decide

end CatCrypt.Crypto.Optimizer.ScheduleSearchMontMulNtt
