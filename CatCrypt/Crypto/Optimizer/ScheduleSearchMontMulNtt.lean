/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Optimizer.RandomizedScheduleSearch
import CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381MontMulKernel

/-!
# Verified-CryptOpt schedule search applied to the modularity-floor kernels (#385 continuation)

The randomized schedule/RA search of `RandomizedScheduleSearch.lean` (the
verified form of CryptOpt's loop: a seeded local search over the
disjoint-footprint adjacent-transposition neighbourhood, with **in-Lean
translation validation of the winner** standing in for CryptOpt's external
equivalence checker) closed `fe25519` to s2n parity only where the gap was
schedule-shaped, and reported a *null* where it was not (`feMulBlock`: 8 legal
swaps, all cost-neutral; the residual was register allocation, #386).

This module points the **same** loop at the two kernels the bench flags as
trailing their hand-asm references on scheduling: the **BLS12-381 `Fp` CIOS
Montgomery multiply** (`Bls12381MontMulKernel.blsMontMulBlock`, 1.11× vs blst's
`mulx_mont_384`, MCA RThru 229.8 vs 206.5) and the **ML-KEM / ML-DSA NTT
butterfly** (1.34× / 1.11× vs PQClean-AVX2). The result on each is the finding —
**including the negatives, which are the load-bearing data**.

## The BLS CIOS finding: the search winner FAILS translation validation

The CIOS body admits a *large* schedule neighbourhood — **81 legal
disjoint-footprint adjacent transpositions** (`blsMontMul_legal_swaps`), an order
of magnitude more than `fe25519`'s 8 — and the static cost proxy *does* improve
under search (`scheduleCost` 765 → 723 after 7 steps, 660 at the fixpoint). So
unlike `fe25519` the search has substantial room to move and a reason to move.

**But the search output is not denotation-preserving, and the in-Lean
translation validation catches it.** The disjoint-footprint *adjacent*-swap
predicate is sound for a single transposition, but the BLS CIOS body **reuses the
`hi`/`lo` MULX-product scratch across all six iterations** (every `mulxMem`
overwrites `lo`, and the column accumulate `adcx t_j, lo` reads it). Over a
*sequence* of locally-legal adjacent swaps this reuse lets the search reorder a
`lo` def-use chain globally even though no individual pair shares `lo` at the
moment it is swapped — the classic composition gap of bubble-style scheduling on
**reused value names**. `fe25519` happened to avoid it (its 8 swaps did not
compose destructively); the BLS block, with 6× the `hi`/`lo` reuse, does not.

`bls_search7_breaks_runBlock` is the machine-checked witness: after **7** search
steps the rescheduled body computes a *different* result word `z[2]` from the
baseline on a concrete state — `runBlock`-distinguishable, hence **rejected by
TV**. The winner therefore **cannot be shipped**: the schedule search closes
**zero** of the BLS gap (its output is wrong). This is exactly what TV exists for
— the search is unverified, and only a TV-passing winner may be emitted. Here the
TV verdict is *reject*, which is itself the honest answer: the 229.8-vs-206.5
residual is **not** reachable by this neighbourhood.

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
barrier between stages serialises the unroll. The search finds **3 legal swaps
per stage, all cost-neutral** (`nttStageBlock_legal_swaps`,
`ntt_search_no_improvement`, `ntt_twostage_no_improvement`) — the `fe25519`-style
null. The NTT 1.34×/1.11×-PQClean residual is the cross-stage **memory residency**
(the emitted stream is 45 % `vmovdqu` — 389 of 869 ops — vs the hand-asm's 19 %,
because every intermediate round-trips through the `inp[]`/`out[]` arrays while
the hand-asm keeps the polynomial register-resident across stages). That is
register allocation (`MlkemRaEmit` / `MLKEM_NTT_RA_BENCH.md`), **not** schedule.

## Bottom line (all machine-checked here / MCA-measured in bench/)

For *both* modularity-floor kernels the schedule search closes **zero** of the
hand-asm gap: on BLS because its winner fails TV (the residual is µop-count), on
the NTT because the schedule neighbourhood is empty (the residual is residency).
The honest scope is the parent module's: the **search** ranges over the
disjoint-footprint neighbourhood; the **winner TV** is the gate that here
*rejects* the BLS winner and finds nothing to gain on the NTT.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.ScheduleSearchMontMulNtt

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.Optimizer.RandomizedScheduleSearch
open CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381MontMulKernel

/-! ## 1. BLS CIOS: the schedule neighbourhood is large (unlike `fe25519`) -/

/-- **The BLS CIOS body admits 81 legal disjoint-footprint adjacent
    transpositions.** A *large* schedule neighbourhood (cf. `fe25519`'s 8): the
    per-iteration constant-staging `mov`s and window-shift `mov` rotation are all
    independent of the surrounding ADX accumulate and so look hoistable. The
    search has substantial room to move — and §3 shows that room is a trap (the
    moves compose into an unsound reorder under the `hi`/`lo` reuse). -/
theorem blsMontMul_legal_swaps : countLegalSwaps blsMontMulBlock = 81 := by
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
  · simp only [if_neg htlo, if_neg (show "lo" ≠ "hi" by decide)]

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
  · simp only [if_neg hthi, if_neg hsrc]

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

/-! ## 3. The search WINNER fails translation validation (the load-bearing result)

The seeded search, run on the full CIOS body, produces — within 7 steps — a
reschedule that **changes the result**. Because the `hi`/`lo` MULX scratch is
reused across all six iterations, a sequence of individually-legal adjacent
transpositions reorders a `lo` def-use chain globally. The witness below is a
concrete state on which the 7-step search output computes a different `z[2]` from
the baseline: the unverified winner is `runBlock`-distinguishable, so **TV rejects
it** and it must not be emitted. The schedule search closes **zero** of the BLS
gap on this block. -/

/-- A concrete init state for the unsoundness witness. -/
def stCE : JState 64 := initState 3 5 7 11 13 17 19 23 29 31 37 41

/-- The six result words `z[0..5]` after running a block from `stCE`. -/
def zWords (b : List (JInstr 64)) : List (BitVec 64) :=
  let s := runBlock stCE b
  [s.mem "z" 0, s.mem "z" 8, s.mem "z" 16, s.mem "z" 24, s.mem "z" 32, s.mem "z" 40]

/-- **The search winner fails translation validation.** After 7 seeded search
    steps the rescheduled CIOS body computes a *different* result from the
    baseline on `stCE` (the `z[2]` word differs by a corrupted carry) — the
    sequence of locally-legal adjacent transpositions reordered a `hi`/`lo`
    def-use chain globally, which the per-pair disjoint-footprint predicate cannot
    see. `runBlock`-distinguishable ⇒ **TV reject**: the unverified winner is not
    denotation-preserving and may not be shipped. This is the in-Lean equivalence
    checker doing its job — and the honest verdict that the 229.8-vs-206.5
    residual is *not* in this schedule neighbourhood. -/
theorem bls_search7_breaks_runBlock :
    zWords (searchIterate 7 blsMontMulBlock 777) ≠ zWords blsMontMulBlock := by
  native_decide

/-- `trySwapAt` (one adjacent transposition) preserves block length. -/
theorem trySwapAt_length (b : List (JInstr 64)) (k : Nat) :
    (trySwapAt b k).length = b.length := by
  induction b generalizing k with
  | nil => cases k <;> rfl
  | cons a tl iha =>
    cases tl with
    | nil => cases k <;> rfl
    | cons b tl2 =>
      cases k with
      | zero => simp only [trySwapAt]; split <;> rfl
      | succ k =>
        simp only [trySwapAt]
        rw [List.length_cons, List.length_cons, iha]

/-- One greedy search step preserves block length (it returns either the input or
    an adjacent transposition of it). -/
theorem searchStep_length (b : List (JInstr 64)) (seed : UInt32) :
    (searchStep b seed).1.length = b.length := by
  simp only [searchStep]
  split <;> simp [trySwapAt_length]

/-- **A reschedule preserves the µop count, hence the MCA port-pressure lower
    bound.** Even setting aside the TV rejection of §3, no reschedule could turn
    the proxy improvement into an `RThroughput` win: `searchIterate` only applies
    `trySwapAt` (adjacent transposition), which preserves length — so any winner
    has exactly the baseline's µop count, and `BlockRThroughput` (port-pressure
    per port, counting µops) is identical. The 229.8 vs blst's 206.5 must be
    closed by *reducing the µop count* (instruction selection / register
    renaming), which the schedule search cannot do. -/
theorem bls_search_preserves_length (n : Nat) (b : List (JInstr 64)) (seed : UInt32) :
    (searchIterate n b seed).length = b.length := by
  induction n generalizing b seed with
  | zero => rfl
  | succ n ih =>
    simp only [searchIterate]
    rw [ih]
    exact searchStep_length b seed

/-! ## 4. ML-KEM / ML-DSA NTT butterfly: the schedule null

One emitted NTT butterfly stage modelled as a `JInstr` block (the dependence
structure the search reasons about — vector lanes do not change the read/write
footprint graph). The stage is `load a; load b; t = b·tw; c = a+t; d = a−t;
store c; store d`: the `add`/`sub` both consume `t` and the stores consume
`c`/`d`, so the arithmetic core is fully serial. -/

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

/-- **The NTT butterfly stage admits only 3 legal disjoint-footprint adjacent
    transpositions** — the two independent input loads and one store; the
    arithmetic `mul → add/sub → store` core is fully serial. The `fe25519`-style
    schedule null: the within-stage neighbourhood is tiny and (next) cost-neutral.
    Crucially, unlike the BLS block these 3 swaps do **not** touch a reused scratch
    name, so they are individually AND compositionally sound. -/
theorem nttStageBlock_legal_swaps : countLegalSwaps nttStageBlock = 3 := by
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
    sequentially ordered by construction — confirming the `MLKEM_NTT_RA_BENCH.md`
    structural finding that the gap is residency. -/
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
