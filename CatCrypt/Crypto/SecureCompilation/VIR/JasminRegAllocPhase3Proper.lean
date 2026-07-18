/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminRegAllocPhase3
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExportPoseidon2

/-!
# Verified register allocation — Phase 3 PROPER

This module closes the two residuals named at the end of the Phase 3-prereq
capstone (`JasminRegAllocPhase3.lean`):

  (a) the **`Lcmd`→`Kernel` reload-event lowering** — the Phase-2/3 capstone
      proves correctness of a body presented as a `Kernel` (`List KBinop`, the
      destructive two-address pair `mov dst, src0; op dst, src1`). A *real*
      spilled body inserts **reload** and **spill** moves (`mov R15, src`,
      `mov dst, R15`) so a binop whose operands are stack slots stays x86-legal.
      We model the four lowering shapes (`LoweredBinop`), give each its concrete
      register-store semantics built from `movStep`/`opStep`/`setReg`, prove
      each denotes `stepBinop` on every non-scratch slot via the existing
      `reload_denote` / `reloadDst_denote` / `reloadBoth_denote` lemmas
      (`JasminLprogExport`:2232–2277), and lift a whole `List LoweredBinop` so
      the Phase-2 `AgreeOnLive` invariant — hence the Phase-3 checked capstone —
      transports to bodies that contain reloads/spills.

  (b) a **checker-accepted coalescing `ρ`** for the 16-lane MDS sub-block that
      broke residence-rename (the slice the orchestrator scales to 107k). The
      Phase-0 `poseidon2ResidenceRho` is *rejected* (the MDS over-collapse — that
      is the whole point of the checker). We give a coalescing `ρ` that the
      *array-backed* `interferenceOkB` **accepts** on the high-pressure MDS
      kernel, with `native_decide` only on the small fixed slice. The full 107k
      `#eval` is the orchestrator's (heavy); we state it and report the command.

`set_option autoImplicit false` is intentionally *not* set (SecureCompilation
convention; see root `CLAUDE.md`).
-/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminRegAllocPhase3Proper

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminRegAllocPhase1
open CatCrypt.Crypto.SecureCompilation.VIR.JasminRegAllocPhase2
open CatCrypt.Crypto.SecureCompilation.VIR.JasminRegAllocPhase3

/-! ## 1. The four reload-lowering shapes of one two-address binop

A logical binop `dst := op src0 src1` is lowered by `legalizeBinop`
(`JasminLprogExport`:983) into ONE of four `Lopn` sequences, depending on which
of `dst`/`src1` are spill (stack) slots:

* `direct` — no spill: `mov dst, src0; op dst, src1`  (= the Phase-1 `stepBinop`);
* `srcReload` — `src1` spilled: `mov dst, src0; mov sc, src1; op dst, sc`
  (route the second source through the reserved scratch `sc`);
* `dstReload` — `dst` spilled: `mov sc, src0; op sc, src1; mov dst, sc`
  (compute in the scratch, store the result back);
* `bothReload` — both spilled: `mov sc, src0; mov sc2, src1; op sc, sc2;
  mov dst, sc` (the two reserved scratches `sc`, `sc2`).

The `sc`/`sc2` are the reserved reload scratches `R15`/`R14`
(`reloadScratch`/`reloadScratch2`): never an allocation target, hence never a
*logical* live slot. We carry them as explicit slot indices so the model is
self-contained. -/

/-- A lowered two-address binop: the logical `KBinop` together with which
    reload shape its `legalizeBinop` produced and the reserved scratch slot(s).
    `sc` is the primary reload scratch (`R15`), `sc2` the secondary (`R14`). -/
inductive LoweredBinop where
  /-- No spill: the direct `mov dst,src0; op dst,src1`. -/
  | direct (b : KBinop)
  /-- Spilled `src1`: route the second source through scratch `sc`. -/
  | srcReload (b : KBinop) (sc : Nat)
  /-- Spilled `dst`: compute in scratch `sc`, store back. -/
  | dstReload (b : KBinop) (sc : Nat)
  /-- Both spilled: scratches `sc` (primary) and `sc2` (secondary). -/
  | bothReload (b : KBinop) (sc sc2 : Nat)

/-- The logical binop a lowered binop realises (forgetting the reload shape). -/
def LoweredBinop.toKBinop : LoweredBinop → KBinop
  | .direct b => b
  | .srcReload b _ => b
  | .dstReload b _ => b
  | .bothReload b _ _ => b

/-- The reserved scratch slots a lowered binop writes (besides `dst`). These must
    be disjoint from every *logical* slot (the reserved `R15`/`R14` are never
    allocation targets). -/
def LoweredBinop.scratch : LoweredBinop → List Nat
  | .direct _ => []
  | .srcReload _ sc => [sc]
  | .dstReload _ sc => [sc]
  | .bothReload _ sc sc2 => [sc, sc2]

/-- **Concrete register-store semantics of one lowered binop**, built directly
    from the `movStep`/`opStep`/`setReg` primitives — exactly the store updates
    the emitted `Lopn` sequence performs. -/
def runLowered {w : Nat} (st : RegStore w) : LoweredBinop → RegStore w
  | .direct b => stepBinop st b
  | .srcReload b sc =>
      -- mov dst, src0 ; mov sc, src1 ; op dst, sc
      let st1 := movStep st b.dst b.src0
      let st2 := movStep st1 sc b.src1
      opStep b.op st2 b.dst sc
  | .dstReload b sc =>
      -- mov sc, src0 ; op sc, src1 ; mov dst, sc
      let st1 := movStep st sc b.src0
      let st2 := opStep b.op st1 sc b.src1
      setReg st2 b.dst (st2 sc)
  | .bothReload b sc sc2 =>
      -- mov sc, src0 ; mov sc2, src1 ; op sc, sc2 ; mov dst, sc
      let st1 := movStep st sc b.src0
      let st2 := movStep st1 sc2 b.src1
      let st3 := opStep b.op st2 sc sc2
      setReg st3 b.dst (st3 sc)

/-- **Scratch well-formedness.** The reserved-scratch disjointness side-conditions
    the emitter maintains, per lowering shape: each scratch differs from the
    binop's `dst` and from its `src1` (so the initial reload of `src0` does not
    clobber `src1`); the two scratches differ from each other. The `direct` shape
    has no obligation. -/
def LoweredBinop.scratchWF : LoweredBinop → Prop
  | .direct b => b.dst ≠ b.src1
  | .srcReload b sc => sc ≠ b.dst ∧ sc ≠ b.src1 ∧ b.dst ≠ b.src1
  | .dstReload b sc => sc ≠ b.dst ∧ sc ≠ b.src1 ∧ b.dst ≠ b.src1
  | .bothReload b sc sc2 =>
      sc ≠ b.dst ∧ sc ≠ b.src1 ∧ sc ≠ sc2 ∧ sc2 ≠ b.dst ∧ b.dst ≠ b.src1

/-! ## 2. Each lowered shape denotes `stepBinop` on every non-scratch slot

The reload moves only ever *read* the original operands and *write* `dst` plus
the reserved scratch(es); so on every slot that is neither `dst` nor a scratch,
the lowered run leaves the store untouched, and on `dst` it computes the same
value `op.apply (st src0) (st src1)` the direct `stepBinop` does. The
side-conditions are exactly the reserved-scratch disjointness the emitter
guarantees (`R15`/`R14` ≠ any operand slot). -/

/-- **Reload-lowering faithfulness.** For every slot `t` that is not a reserved
    scratch of `lb`, the reload-lowered run agrees with the plain two-address
    `stepBinop` on the underlying logical binop. The side-conditions name the
    reserved-scratch disjointness the emitter maintains: the scratch slots differ
    from `dst`, from `src1` (so the initial reload does not clobber `src1`), and
    from each other. -/
theorem runLowered_eq_stepBinop {w : Nat} (st : RegStore w) (lb : LoweredBinop)
    (hsc : lb.scratchWF) (t : Nat) (ht : t ∉ lb.scratch) :
    runLowered st lb t = stepBinop st lb.toKBinop t := by
  cases lb with
  | direct b => rfl
  | srcReload b sc =>
      obtain ⟨hscd, hsc1, hncb⟩ := hsc
      simp only [LoweredBinop.scratch, List.mem_singleton] at ht
      by_cases htd : t = b.dst
      · subst htd
        -- both compute op.apply (st src0) (st src1) at dst
        simp only [runLowered, stepBinop, LoweredBinop.toKBinop, opStep, movStep,
          setReg, if_true, if_neg (Ne.symm hscd : ¬ b.dst = sc),
          if_neg (Ne.symm hncb : ¬ b.src1 = b.dst)]
      · simp only [runLowered, stepBinop, LoweredBinop.toKBinop, opStep, movStep,
          setReg, if_neg htd, if_neg ht]
  | dstReload b sc =>
      obtain ⟨hscd, hsc1, hncb⟩ := hsc
      simp only [LoweredBinop.scratch, List.mem_singleton] at ht
      by_cases htd : t = b.dst
      · subst htd
        simp only [runLowered, LoweredBinop.toKBinop]
        rw [reloadDst_denote b.op st b.dst b.src0 b.src1 sc hsc1]
        simp only [stepBinop, opStep, movStep, setReg, if_true,
          if_neg (Ne.symm hncb : ¬ b.src1 = b.dst)]
      · simp only [runLowered, stepBinop, LoweredBinop.toKBinop, opStep, movStep,
          setReg, if_neg htd, if_neg ht]
  | bothReload b sc sc2 =>
      obtain ⟨hscd, hsc1, hsc12, hsc2d, hncb⟩ := hsc
      simp only [LoweredBinop.scratch, List.mem_cons,
        List.not_mem_nil, or_false, not_or] at ht
      obtain ⟨htsc, htsc2⟩ := ht
      by_cases htd : t = b.dst
      · subst htd
        simp only [runLowered, LoweredBinop.toKBinop]
        rw [reloadBoth_denote b.op st b.dst b.src0 b.src1 sc sc2 hsc1 hsc12]
        simp only [stepBinop, opStep, movStep, setReg, if_true,
          if_neg (Ne.symm hncb : ¬ b.src1 = b.dst)]
      · simp only [runLowered, stepBinop, LoweredBinop.toKBinop, opStep, movStep,
          setReg, if_neg htd, if_neg htsc, if_neg htsc2]

/-! ## 3. Lifting to a whole lowered body

A **lowered body** is a `List LoweredBinop`: the spilled-and-legalized straight
line the emitter actually produces. It projects to the logical `Kernel` it
realises (`loweredKernel`, the kernel the Phase-3 checker runs on), and runs
left-to-right through `runLowered` (`runLoweredBody`). On every slot disjoint
from all reload scratches, the lowered run equals the plain kernel run — so the
Phase-2 `AgreeOnLive` invariant (over *logical* live slots, all disjoint from the
reserved scratches) transports verbatim. -/

/-- The logical `Kernel` a lowered body realises (forget every reload shape). -/
def loweredKernel (lbs : List LoweredBinop) : Kernel := lbs.map LoweredBinop.toKBinop

/-- Run a whole lowered body left-to-right (the spilled/legalized straight line). -/
def runLoweredBody {w : Nat} (st : RegStore w) (lbs : List LoweredBinop) : RegStore w :=
  lbs.foldl runLowered st

@[simp] theorem runLoweredBody_nil {w : Nat} (st : RegStore w) :
    runLoweredBody st [] = st := rfl

@[simp] theorem runLoweredBody_cons {w : Nat} (st : RegStore w)
    (lb : LoweredBinop) (lbs : List LoweredBinop) :
    runLoweredBody st (lb :: lbs) = runLoweredBody (runLowered st lb) lbs := rfl

@[simp] theorem loweredKernel_cons (lb : LoweredBinop) (lbs : List LoweredBinop) :
    loweredKernel (lb :: lbs) = lb.toKBinop :: loweredKernel lbs := rfl

/-- Every binop of a lowered body is scratch-well-formed. -/
def bodyScratchWF (lbs : List LoweredBinop) : Prop := ∀ lb ∈ lbs, lb.scratchWF

/-! ### The reloads are observationally invisible on scratch-free slots

The keystone: running the spilled/legalized **lowered body** `lbs` is, on every
slot disjoint from all reload scratches, *the same store* as running the plain
two-address `loweredKernel lbs`. The reload/spill moves only shuttle values
through the reserved scratches; they never perturb a logical slot's value. So the
Phase-2/3 theorems — stated for `runKernel` over the plain kernel — read off the
real lowered body unchanged on the (scratch-free) logical live/output slots. -/

/-- A predicate fixing a **global reserved-scratch set** `S` disjoint from every
    *logical* operand of the body: every binop's reload scratches lie in `S`, and
    no binop's `dst`/`src0`/`src1` lies in `S`. With the real emitter `S =
    {R15,R14}` and the logical slots are the residence classes — disjoint by
    construction (the scratches are never allocation targets). -/
def scratchSepOn (S : Nat → Prop) (lbs : List LoweredBinop) : Prop :=
  ∀ lb ∈ lbs,
    (∀ s ∈ lb.scratch, S s) ∧
    ¬ S lb.toKBinop.dst ∧ ¬ S lb.toKBinop.src0 ∧ ¬ S lb.toKBinop.src1

/-- **Pointwise lowered = kernel agreement, propagated.** Two stores `stL` (the
    lowered run so far) and `stK` (the kernel run so far) that agree on every
    non-scratch slot stay agreeing on every non-scratch slot after running the
    rest of the body on each. The reads each step makes are logical operands
    (non-scratch, where the stores agree), and each step's only non-scratch write
    is `dst`, set to the same value on both sides; scratch writes stay inside `S`.
    Hence the final stores agree off `S` — in particular on the output slots. -/
theorem runLowered_runKernel_agree_off {w : Nat} (S : Nat → Prop)
    (lbs : List LoweredBinop) (hwf : bodyScratchWF lbs) (hsep : scratchSepOn S lbs)
    (stL stK : RegStore w) (hstart : ∀ t, ¬ S t → stL t = stK t) :
    ∀ t, ¬ S t → runLoweredBody stL lbs t = runKernel stK (loweredKernel lbs) t := by
  induction lbs generalizing stL stK with
  | nil => intro t ht; simpa using hstart t ht
  | cons lb rest ih =>
      intro t ht
      simp only [runLoweredBody_cons, loweredKernel_cons, runKernel_cons]
      have hwflb : lb.scratchWF := hwf lb List.mem_cons_self
      have hwfrest : bodyScratchWF rest := fun b hb => hwf b (List.mem_cons_of_mem _ hb)
      have hseplb := hsep lb List.mem_cons_self
      have hseprest : scratchSepOn S rest := fun b hb => hsep b (List.mem_cons_of_mem _ hb)
      -- The stepped stores agree off S: feed them to the IH.
      refine ih hwfrest hseprest (runLowered stL lb) (stepBinop stK lb.toKBinop) ?_ t ht
      intro u hu
      -- `u ∉ S`, so `u` is not a scratch of `lb` (scratches are in S).
      have huscr : u ∉ lb.scratch := fun hmem => hu (hseplb.1 u hmem)
      -- the lowered step on stL equals the kernel step on stL at u …
      rw [runLowered_eq_stepBinop stL lb hwflb u huscr]
      -- … and the kernel step preserves the start agreement: both `stepBinop`s
      -- read only `dst,src0,src1` (non-scratch, where stL,stK agree) and write dst.
      by_cases hud : u = lb.toKBinop.dst
      · subst hud
        simp only [stepBinop, opStep, movStep, setReg, if_true,
          hstart lb.toKBinop.src0 hseplb.2.2.1, hstart lb.toKBinop.src1 hseplb.2.2.2]
      · simp only [stepBinop, opStep, movStep, setReg, if_neg hud]
        exact hstart u hu

/-! ## 4. The capstone applies to a real spilled (reloaded) body

Composing §3 with the Phase-3 checked capstone `runKernel_allocKernel_checked`:
if a lowered body `lbs` *realises the allocated kernel* `allocKernel ρ k` (i.e.
`loweredKernel lbs = allocKernel ρ k` — the producer emits the ρ-renamed kernel
with reloads spliced in), the array checker accepts ρ on the sinked logical
trace, and the reserved scratch set `S` is disjoint from every physical operand,
then the **lowered body's run** agrees through ρ with the naive kernel run on
every output slot. The reloads/spills are observationally invisible (§3); the ρ
collapse is sound (Phase 2/3). This is the Phase-3 capstone for bodies-with-reloads. -/

/-- **Checked allocation correctness for a spilled/reloaded body.** Let `lbs` be
    the lowered (legalized, reload-bearing) emission of the allocated kernel
    `allocKernel ρ k` — `hreal : loweredKernel lbs = allocKernel ρ k`. If

    * the Phase-0 array checker accepts ρ on the sinked logical trace (`hir`),
    * the per-binop no-clobber Boolean passes (`hnc`),
    * the body is scratch-well-formed (`hwf`) with all reload scratches inside a
      reserved set `S` disjoint from every physical operand (`hsep`),
    * the allocated start store `stL` and the naive start store `st` agree
      through ρ on the seeded live-in, and `stL` is the lowered run's start
      (agreeing with the kernel's allocated start `st'` off `S`, `hstartLS`),

    then for every output slot `s ∈ L0` the **lowered body** lands `ρ s`'s value
    equal to the naive run's `s`. `ρ` is not assumed injective. -/
theorem runLoweredBody_checked {w : Nat} (L0 : List Nat) (ρ : Nat → Nat)
    (k : Kernel) (S : Nat → Prop)
    (lbs : List LoweredBinop) (hreal : loweredKernel lbs = allocKernel ρ k)
    (hwf : bodyScratchWF lbs) (hsep : scratchSepOn S lbs)
    (hir : interferenceOkB (sinkedTrace L0 k) ρ = true)
    (hnc : allBinopsNoClobberB ρ k = true)
    (stL st' st : RegStore w)
    (hSL : ∀ t, ¬ S t → stL t = st' t)
    (hstart : AgreeOnLive ρ st' st (liveInSeeded L0 k))
    (s : Nat) (hs : s ∈ L0) (hsS : ¬ S (ρ s)) :
    (runLoweredBody stL lbs) (ρ s) = (runKernel st k) s := by
  -- (1) lowered run = allocated-kernel run on ρ s (off S).
  have h1 : (runLoweredBody stL lbs) (ρ s) = (runKernel st' (loweredKernel lbs)) (ρ s) :=
    runLowered_runKernel_agree_off S lbs hwf hsep stL st' hSL (ρ s) hsS
  -- (2) allocated-kernel run = naive run on ρ s (Phase-3 checked capstone).
  have h2 : (runKernel st' (allocKernel ρ k)) (ρ s) = (runKernel st k) s :=
    output_agree_of_checked L0 ρ k hir hnc st' st hstart s hs
  rw [h1, hreal, h2]

/-! ## 5. Piece (b): a checker-accepted coalescing ρ for the 16-lane MDS block

The 4×4 external-MDS column-sum is the high-pressure pattern that broke the
107k residence rename (the `recColSums` over-collapse): 16 lane inputs, four
column sums `sums[k] = s[k]+s[k+4]+s[k+8]+s[k+12]`, each added back to its four
lanes. All 16 lanes are simultaneously live across the column-sum window — so a
ρ that collapses two *coexisting* lanes is rejected (exactly
`poseidon2ResidenceRho` on the full body). This slice is the in-Phase-1 16-lane
sub-block (`emitColSums` shape); we give a **coalescing** ρ the checker accepts.

Slot convention (fresh SSA):

* inputs:   lanes `s[0..15]` = slots `0..15`;
* products: column sums `c0=16, c1=17, c2=18, c3=19`;
* outputs:  `y[0..15] = 20..35`  (`y[i] = s[i] + c[i mod 4]`).

Naive: 36 distinct slots. The accepted coalescing reuses **each lane's own home
for its output** (`y[i] → s[i]`: lane `i` is read for the last time at the binop
producing `y[i]`), collapsing to **20** physical slots while keeping every pair
of simultaneously-live values distinct. The four column sums `c0..c3` must stay
on their own slots (they are live across all 16 output writes), so over-collapsing
any `c` onto a lane is rejected. -/

/-- The 16-lane external-MDS column-sum kernel: four column sums then 16 lane
    write-backs `y[i] = s[i] + c[i mod 4]`. The pattern that broke residence
    rename, as a self-contained `Kernel`. -/
def colSum16Kernel : Kernel :=
  [ -- column sums (all 16 lanes live)
    { dst := 16, op := .add, src0 := 0,  src1 := 4 },
    { dst := 16, op := .add, src0 := 16, src1 := 8 },
    { dst := 16, op := .add, src0 := 16, src1 := 12 },   -- c0 in slot 16
    { dst := 17, op := .add, src0 := 1,  src1 := 5 },
    { dst := 17, op := .add, src0 := 17, src1 := 9 },
    { dst := 17, op := .add, src0 := 17, src1 := 13 },    -- c1 in slot 17
    { dst := 18, op := .add, src0 := 2,  src1 := 6 },
    { dst := 18, op := .add, src0 := 18, src1 := 10 },
    { dst := 18, op := .add, src0 := 18, src1 := 14 },    -- c2 in slot 18
    { dst := 19, op := .add, src0 := 3,  src1 := 7 },
    { dst := 19, op := .add, src0 := 19, src1 := 11 },
    { dst := 19, op := .add, src0 := 19, src1 := 15 },    -- c3 in slot 19
    -- per-lane write-backs y[i] = s[i] + c[i mod 4]  (lane i read last here)
    { dst := 20, op := .add, src0 := 0,  src1 := 16 },
    { dst := 21, op := .add, src0 := 1,  src1 := 17 },
    { dst := 22, op := .add, src0 := 2,  src1 := 18 },
    { dst := 23, op := .add, src0 := 3,  src1 := 19 },
    { dst := 24, op := .add, src0 := 4,  src1 := 16 },
    { dst := 25, op := .add, src0 := 5,  src1 := 17 },
    { dst := 26, op := .add, src0 := 6,  src1 := 18 },
    { dst := 27, op := .add, src0 := 7,  src1 := 19 },
    { dst := 28, op := .add, src0 := 8,  src1 := 16 },
    { dst := 29, op := .add, src0 := 9,  src1 := 17 },
    { dst := 30, op := .add, src0 := 10, src1 := 18 },
    { dst := 31, op := .add, src0 := 11, src1 := 19 },
    { dst := 32, op := .add, src0 := 12, src1 := 16 },
    { dst := 33, op := .add, src0 := 13, src1 := 17 },
    { dst := 34, op := .add, src0 := 14, src1 := 18 },
    { dst := 35, op := .add, src0 := 15, src1 := 19 } ]

/-- The fresh-SSA trace of the 16-lane column-sum kernel. -/
def colSum16Trace : List PhysEvent := kernelTrace colSum16Kernel

/-- The output slots kept live by the sink: `y[0..15]` = slots `20..35`. -/
def colSum16Outputs : List Nat := (List.range 16).map (· + 20)

/-- **The accepted coalescing allocation.** Reuse each lane's home for its own
    output (`y[i] = s[i] + c[i mod 4]` → slot `i`): lane `i` is dead right after
    `y[i]`, and `y[i]`'s second source is `c[i mod 4]` (a distinct column-sum
    slot), so no `dst = src1` clobber. Column sums keep their own slots `16..19`
    (live across all write-backs). Homes: `{0..19}` = 20 physical slots, vs the
    naive 36. -/
def colSum16Rho : Nat → Nat := fun n =>
  if 20 ≤ n ∧ n ≤ 35 then n - 20  -- y[i] reuses lane i's home
  else n                          -- lanes 0..15 and column sums 16..19 fixed

/-! ### (b) the array checker ACCEPTS the coalescing ρ on the 16-lane slice -/

/-- **(b) the array-backed `interferenceOkB` accepts the coalescing ρ** on the
    sinked 16-lane MDS slice (a `native_decide` over the fixed 28-binop sinked
    trace — NOT a loop-running denotation fold). The 16 simultaneously-live lanes
    and 4 column sums stay on 20 distinct homes; the def-clobbers-live-out edge
    is satisfied at every point. -/
theorem colSum16_interferenceOkB :
    interferenceOkB (sinkedTrace colSum16Outputs colSum16Kernel) colSum16Rho = true := by
  native_decide

/-- **(b) the no-clobber Boolean passes** under the coalescing ρ. -/
theorem colSum16_noClobberB :
    allBinopsNoClobberB colSum16Rho colSum16Kernel = true := by native_decide

/-- **(b) the slot win:** the coalescing ρ uses strictly fewer physical slots. -/
theorem colSum16_naive_slot_count : naiveSlotCount colSum16Kernel = 36 := by native_decide

theorem colSum16_alloc_slot_count : allocSlotCount colSum16Rho colSum16Kernel = 20 := by
  native_decide

theorem colSum16_fewer_slots :
    allocSlotCount colSum16Rho colSum16Kernel < naiveSlotCount colSum16Kernel := by
  rw [colSum16_alloc_slot_count, colSum16_naive_slot_count]; decide

/-- **(b) the over-collapse the residence rename did IS rejected.** Aliasing two
    simultaneously-live lanes (here `s[4] → s[0]`'s home, both live across the
    `c0` sum) is rejected by the array checker — the MDS-simultaneity edge, the
    exact failure mode of `poseidon2ResidenceRho`. -/
def colSum16RhoBad : Nat → Nat := fun n => if n = 4 then 0 else colSum16Rho n

theorem colSum16_badRho_rejected :
    interferenceOkB (sinkedTrace colSum16Outputs colSum16Kernel) colSum16RhoBad = false := by
  native_decide

/-! ### (b) the Phase-3 checked capstone fires on the 16-lane slice

`runKernel_allocKernel_checked` (Phase 3) applied to the coalescing ρ: starting
from stores agreeing through ρ on the seeded live-in (the 16 input lanes), the
20-slot allocated run agrees with the 36-slot naive run on every output. -/

/-- The seeded live-in of the 16-lane slice is exactly the 16 input lanes
    `{0..15}` — a finite membership check (order-independent). -/
theorem colSum16_liveInSeeded_all :
    (liveInSeeded colSum16Outputs colSum16Kernel).all (fun s => s < 16) = true := by
  native_decide

theorem colSum16_liveInSeeded (s : Nat)
    (hs : s ∈ liveInSeeded colSum16Outputs colSum16Kernel) : s < 16 := by
  have := (List.all_eq_true.mp colSum16_liveInSeeded_all) s hs
  simpa using this

/-- **(b) whole-slice checked correctness.** The 20-slot allocated column-sum run
    agrees through `colSum16Rho` with the 36-slot naive run on every output slot
    `y[0..15]` (= `20..35`), via the Phase-3 array-checked capstone — no per-slot
    symbolic evaluation, `ρ` not injective. -/
theorem colSum16_outputs_checked {w : Nat} (st' st : RegStore w)
    (hstart : AgreeOnLive colSum16Rho st' st (liveInSeeded colSum16Outputs colSum16Kernel)) :
    ∀ s ∈ colSum16Outputs,
      (runKernel st' (allocKernel colSum16Rho colSum16Kernel)) (colSum16Rho s)
        = (runKernel st colSum16Kernel) s :=
  fun s hs =>
    runKernel_allocKernel_checked colSum16Outputs colSum16Rho colSum16Kernel
      colSum16_interferenceOkB colSum16_noClobberB st' st hstart s hs

/-! ## 6. End-to-end demo: the capstone fires on a REAL reloaded body

We lower the allocated MDS kernel `allocKernel mds4Rho mds4Kernel` with genuine
reload events spliced in — the first binop routed through a `srcReload`, one
through a `dstReload`, one through a `bothReload` — using reserved scratch slots
`100,101` (disjoint from the physical homes `0..6`). The reserved-scratch set is
`S t := 100 ≤ t`. We then show the Phase-3-proper capstone
`runLoweredBody_checked` lands every MDS output through `mds4Rho` equal to the
naive run, on the genuinely spilled body. -/

/-- The reserved scratch set for the demo: slots `≥ 100`, disjoint from the MDS
    physical homes `0..6` and outputs. -/
def demoScratch : Nat → Prop := fun t => 100 ≤ t

/-- A lowered emission of `allocKernel mds4Rho mds4Kernel` with real reloads: the
    three output binops are routed through reserved scratches `100`/`101` (a
    `srcReload`, a `dstReload`, a `bothReload`); the rest are `direct`. Its
    `loweredKernel` is exactly the allocated kernel. -/
def mds4LoweredBody : List LoweredBinop :=
  (allocKernel mds4Rho mds4Kernel).map LoweredBinop.direct
    |>.set 3 (.srcReload (KBinop.alloc mds4Rho ⟨7, .add, 0, 6⟩) 100)
    |>.set 4 (.dstReload (KBinop.alloc mds4Rho ⟨8, .add, 1, 6⟩) 100)
    |>.set 5 (.bothReload (KBinop.alloc mds4Rho ⟨9, .add, 2, 6⟩) 100 101)

/-- The lowered demo body realises the allocated kernel (reloads forgotten). -/
theorem mds4LoweredBody_real :
    loweredKernel mds4LoweredBody = allocKernel mds4Rho mds4Kernel := by
  native_decide

/-- The demo body is scratch-well-formed (the reserved-scratch disjointness the
    emitter maintains). -/
theorem mds4LoweredBody_wf : bodyScratchWF mds4LoweredBody := by
  intro lb hlb
  fin_cases hlb <;>
    simp_all [LoweredBinop.scratchWF, KBinop.alloc, mds4Rho]

/-- Every reload scratch of the demo body lies in `demoScratch`, and no physical
    operand does. -/
theorem mds4LoweredBody_sep : scratchSepOn demoScratch mds4LoweredBody := by
  intro lb hlb
  fin_cases hlb <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp_all [demoScratch, LoweredBinop.scratch, LoweredBinop.toKBinop,
      KBinop.alloc, mds4Rho]

/-- **End-to-end: the capstone fires on the spilled MDS body.** Starting from a
    lowered start store `stL` agreeing off `demoScratch` with an allocated start
    `st'` that agrees through `mds4Rho` with the naive start on the four input
    lanes, the **reloaded** body lands every output `y[i]` (slots `7..10`) at
    `mds4Rho`-home equal to the naive run. The reloads are invisible (§3); the
    7-slot collapse is sound (Phase 2/3). -/
theorem mds4LoweredBody_outputs {w : Nat} (stL st' st : RegStore w)
    (hSL : ∀ t, ¬ demoScratch t → stL t = st' t)
    (hstart : AgreeOnLive mds4Rho st' st (liveInSeeded mds4Outputs mds4Kernel)) :
    ∀ s ∈ mds4Outputs,
      (runLoweredBody stL mds4LoweredBody) (mds4Rho s) = (runKernel st mds4Kernel) s := by
  intro s hs
  refine runLoweredBody_checked mds4Outputs mds4Rho mds4Kernel demoScratch
    mds4LoweredBody mds4LoweredBody_real mds4LoweredBody_wf mds4LoweredBody_sep
    mds4_interferenceOkB mds4_noClobberB stL st' st hSL hstart s hs ?_
  -- `mds4Rho s < 7 ≤ 99 < 100`, so `ρ s ∉ demoScratch`.
  fin_cases hs <;> simp [demoScratch, mds4Rho]

/-! ## 7. The full-107k orchestrator hook (heavy `#eval`, run by the orchestrator)

The slice above (`colSum16Kernel`) is the in-Lean, `native_decide`-checkable
16-lane MDS sub-block: a coalescing ρ that the array checker provably accepts
(36→20 slots), the over-collapse provably rejected. The **full 107k** body is the
orchestrator's heavy `#eval` (a compiled run, not an in-kernel `native_decide`;
#512-class). Two named `Bool` entry points the orchestrator can `#eval` on the
compiled exe:

* `poseidon2ResidenceCheck` (in `JasminLprogExportPoseidon2`) — the *rejected*
  `proposedRho slotTraceArr`; expected `false` (the MDS over-collapse).
* `poseidon2IdentityCheck` — the identity positive control; expected `true`.

A *checker-accepted coalescing* ρ for the full body — one that collapses the
≈107 000 SSA names onto few classes yet the array `interferenceOkB` accepts — is
the genuine open coalescing-allocator deliverable. What it needs (read off the
slice's accepting ρ and the rejected residence ρ): the residence map
`proposedRho slotTraceArr` is rejected because the `emitApplyMat4` / `emitColSums`
staging parks values in `tmp2,tmp4,acc0,acc1,prod0,prod1` (slots `19..24`) that
are simultaneously live with the 16 lanes across the MDS window — the residence
map (keyed on binding ordinal → its `Fin 25` slot) can re-enter a logical slot
while a *previous* value in that slot is still needed by a later MDS row. The fix
the slice demonstrates is a **per-class split**: the over-collapsed MDS scratch
classes must be widened to fresh classes (beyond the 25-slot residence universe)
for the duration of the MDS window, exactly as the slice keeps the four column
sums `16..19` on their own homes while every lane keeps its own. A linear-scan
that splits *only* the rejected scratch classes (leaving the 16 lanes + reduction
scratch coalesced) is the remaining allocator work; its output ρ is then run
through this same `interferenceOkB` for verified acceptance.

We do **not** assert a theorem that any full-107k ρ is accepted (that would
require the heavy `#eval`, and asserting acceptance without running the checker
would be unsound). We expose the orchestrator command below. -/

/-- Orchestrator `#eval` entry: the full-107k Phase-0 array checker on the
    *identity* map (positive control). Expected `true` — the fresh-SSA body is
    intrinsically allocatable; the rejection of the residence collapse is the
    proposal's fault, not the body's. (Same as
    `JasminLprogExportPoseidon2.poseidon2IdentityCheck`, re-exported here so the
    Phase-3-proper orchestrator step is self-contained.)

    Orchestrator command:
    `#eval CatCrypt.Crypto.SecureCompilation.VIR.JasminRegAllocPhase3Proper.poseidon2FullIdentityCheck`
    (expect `true`). -/
def poseidon2FullIdentityCheck : Bool :=
  CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.poseidon2IdentityCheck

/-- Orchestrator `#eval` entry: the full-107k Phase-0 array checker on the
    proposed residence collapse `proposedRho slotTraceArr`. Expected `false` —
    the MDS over-collapse (the slice's `colSum16RhoBad` analogue at scale).

    Orchestrator command:
    `#eval CatCrypt.Crypto.SecureCompilation.VIR.JasminRegAllocPhase3Proper.poseidon2FullResidenceCheck`
    (expect `false`). -/
def poseidon2FullResidenceCheck : Bool :=
  CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.poseidon2ResidenceCheck

end CatCrypt.Crypto.SecureCompilation.VIR.JasminRegAllocPhase3Proper
