/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminRegAllocPhase2

/-!
# Verified register allocation — Phase 3 prerequisite (generic Boolean bridge)

Phase 2 (`JasminRegAllocPhase2.lean`) proved the general whole-body theorem
`runKernel_allocKernel_live`, but it takes an **abstract**
`InterferenceRespectedSeeded L0 ρ k` hypothesis. Phase 2 discharged that
hypothesis for the *concrete* `mds4` kernel via a direct `native_decide` over a
small Boolean table (`interferenceSeededB`). That per-kernel `native_decide`
does not scale: at the 107k-binop Poseidon2 body it never runs.

Phase 0 (`JasminLprogExport.lean`) provides an **array-backed** Boolean checker
`interferenceOkB` (with `liveOuts` `@[implemented_by]` a rolling-set pass
`liveOutsImpl`) that *does* handle the 107k body without stack overflow.

This module is the missing **generic** bridge:

  `interferenceOkB (kernelTrace k ++ [sinkEvent L0]) ρ = true`
      `⇒  InterferenceRespectedSeeded L0 ρ k`

connecting the scalable Phase-0 array checker to the Phase-2 general theorem.
Concretely it shows the Phase-0 backward `liveAux`/`liveOuts` pass over the
sinked kernel trace **is** the Phase-2 seeded backward pass `liveInSeeded`,
so a slot-assignment accepted by the compiled checker provably satisfies the
denotation-preserving allocation theorem at any scale.

## The sink event and the live-out alignment

`sinkEvent L0` is a final pseudo-event reading the output slots `L0` (so they
stay live to the very end of the kernel). The Phase-0 `liveAux` cons clause for
`ev = b.toEvent` (`wr = b.dst`, `rds = [b.src0, b.src1]`) is **definitionally**
the Phase-2 `liveInSeeded` cons clause, so:

* `liveAuxKernel_eq` : `(liveAux (kernelTrace k ++ tail)).1 = liveInSeeded (liveAux tail).1 k`
* `liveOutsKernel_get` : the `i`-th Phase-0 live-out of the sinked trace
  (for `i < k.length`) is the Phase-2 `liveInSeeded L0` of the suffix `k.drop (i+1)`.

The interference check at point `i` is over `{b_i.dst} ∪ liveOut_i`, which is
exactly the seeded def-clobbers-live-out edge.

`set_option autoImplicit false` is intentionally *not* set (SecureCompilation
convention; see root `CLAUDE.md`).
-/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminRegAllocPhase3

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminRegAllocPhase1
open CatCrypt.Crypto.SecureCompilation.VIR.JasminRegAllocPhase2

/-! ## 1. The output sink event

A single pseudo-event reading the kept-live output slots `L0`. Its `wr` is
irrelevant to the analysis (it is the last event, so its live-out is `∅`, and
its own live-in is `(∅.filter _) ++ L0 = L0`). -/

/-- The sink reads the output slots `L0`; its destination is a sentinel slot that
    plays no role (it is never read downstream, the sink being last). -/
def sinkEvent (L0 : List Nat) : PhysEvent := { wr := 0, rds := L0 }

/-- The sinked fresh-SSA trace of a kernel: the kernel trace followed by the
    output sink. This is exactly the trace the Phase-0 array checker runs on. -/
def sinkedTrace (L0 : List Nat) (k : Kernel) : List PhysEvent :=
  kernelTrace k ++ [sinkEvent L0]

@[simp] theorem liveAux_sink (L0 : List Nat) :
    liveAux [sinkEvent L0] = (L0, [([] : List Nat)]) := by
  simp [liveAux, sinkEvent]

/-! ## 2. The Phase-0 backward pass over a kernel trace IS the seeded pass

The Phase-0 `liveAux` cons clause for `b.toEvent` is definitionally the Phase-2
`liveInSeeded` cons clause. Threading the analysis over `kernelTrace k ++ tail`
seeds the kernel's backward pass with the live-in of `tail`. -/

/-- The live-in produced by the Phase-0 backward pass over the kernel trace
    (seeded by `tail`'s live-in) equals the Phase-2 seeded live-in. -/
theorem liveAux_kernelTrace_append (k : Kernel) (tail : List PhysEvent) :
    (liveAux (kernelTrace k ++ tail)).1 = liveInSeeded (liveAux tail).1 k := by
  induction k with
  | nil => simp [kernelTrace, liveInSeeded]
  | cons b rest ih =>
      simp only [kernelTrace, List.map_cons, List.cons_append]
      rw [liveAux]
      rcases hp : liveAux ((rest.map KBinop.toEvent) ++ tail) with ⟨succIn, outsRest⟩
      have hsucc : succIn = liveInSeeded (liveAux tail).1 rest := by
        have := ih; rw [kernelTrace, hp] at this; exact this
      subst hsucc
      simp only [liveInSeeded_cons, KBinop.toEvent]

/-- Specialised to the sink: the kernel's seeded live-in. -/
theorem liveAux_sinkedTrace (L0 : List Nat) (k : Kernel) :
    (liveAux (sinkedTrace L0 k)).1 = liveInSeeded L0 k := by
  unfold sinkedTrace
  rw [liveAux_kernelTrace_append, liveAux_sink]

/-! ## 3. Per-point live-out alignment

The Phase-0 `liveOuts` of the sinked trace, at each kernel index `i`, equals the
Phase-2 `liveInSeeded L0` of the remaining suffix `k.drop (i+1)`. We package the
recursion: the live-out list of `kernelTrace (b :: rest) ++ tail` starts with the
live-in of `kernelTrace rest ++ tail` (= the seeded live-in of `rest`). -/

/-- The live-out list of the sinked trace, recursively. The head event's
    live-out is the live-in of the remaining (sinked) suffix. -/
theorem liveOuts_kernelTrace_cons (b : KBinop) (rest : Kernel) (tail : List PhysEvent) :
    liveAux (kernelTrace (b :: rest) ++ tail)
      = ((liveInSeeded (liveAux tail).1 (b :: rest)),
          (liveAux (kernelTrace rest ++ tail)).1 ::
            (liveAux (kernelTrace rest ++ tail)).2) := by
  have hrec : (liveAux (kernelTrace rest ++ tail)).1 = liveInSeeded (liveAux tail).1 rest :=
    liveAux_kernelTrace_append rest tail
  simp only [kernelTrace, List.map_cons, List.cons_append]
  rw [liveAux]
  -- destructure the recursive call so the match reduces
  rcases hp : liveAux ((rest.map KBinop.toEvent) ++ tail) with ⟨succIn, outsRest⟩
  simp only []
  have hsucc : succIn = liveInSeeded (liveAux tail).1 rest := by
    have := hrec; rw [kernelTrace] at this; rw [hp] at this; exact this
  subst hsucc
  simp only [liveInSeeded_cons, KBinop.toEvent]

/-! ## 4. The generic interference bridge

We walk the zipped `(event, live-out)` pairs of the sinked trace. Each kernel
point `(b.toEvent, liveOut)` carries `liveOut = liveInSeeded L0 rest` for its
suffix `rest`; the Phase-0 point check (`{b.dst} ∪ liveOut` pairwise-distinct
under `ρ`) yields the seeded def-clobbers-live-out edge
`∀ t ∈ liveInSeeded L0 rest, t ≠ b.dst → ρ t ≠ ρ b.dst`. The trailing sink point
contributes nothing to the kernel's certificate. -/

/-- **Per-suffix interference from the Phase-0 zipped certificate.** If the
    Phase-0 point-check holds on every `(event, live-out)` pair of the sinked
    trace, then the Phase-2 seeded interference proposition holds for the kernel.
    Proved by induction relating the zip to the seeded backward pass. -/
theorem interferenceSeeded_of_interferenceOkB (L0 : List Nat) (ρ : Nat → Nat)
    (k : Kernel) (h : interferenceOkB (sinkedTrace L0 k) ρ = true) :
    InterferenceRespectedSeeded L0 ρ k := by
  induction k with
  | nil => trivial
  | cons b rest ih =>
      -- Unfold the zipped checker on the (b :: rest) sinked trace.
      have hzip : (sinkedTrace L0 (b :: rest)).zip (liveOuts (sinkedTrace L0 (b :: rest)))
          = (b.toEvent, liveInSeeded L0 rest)
              :: (sinkedTrace L0 rest).zip (liveOuts (sinkedTrace L0 rest)) := by
        have hsucc : (liveAux (kernelTrace rest ++ [sinkEvent L0])).1 = liveInSeeded L0 rest := by
          rw [liveAux_kernelTrace_append rest [sinkEvent L0], liveAux_sink]
        unfold sinkedTrace liveOuts
        rw [liveOuts_kernelTrace_cons b rest [sinkEvent L0], liveAux_sink]
        simp only [kernelTrace, List.map_cons, List.cons_append]
        rw [List.zip_cons_cons]
        rw [show (liveAux (List.map KBinop.toEvent rest ++ [sinkEvent L0])).1
              = liveInSeeded L0 rest from by rw [← kernelTrace]; exact hsucc]
      -- The head point-check gives the seeded def-clobbers-live-out edge.
      rw [interferenceOkB, hzip] at h
      rw [List.all_cons, Bool.and_eq_true] at h
      obtain ⟨hhead, htail⟩ := h
      -- Reassemble the tail certificate and recurse.
      have htail' : interferenceOkB (sinkedTrace L0 rest) ρ = true := by
        rw [interferenceOkB]; exact htail
      refine ⟨?_, ih htail'⟩
      -- Extract the head edge from the point-check.
      intro t ht htd
      -- `hhead : liveSetInterferenceOkB ρ (b.toEvent.wr :: liveInSeeded L0 rest) = true`.
      -- Unfold the outer/inner `all`: the `a = b.dst` row's cross-check against
      -- the live-out member `t` is `if b.dst == t then true else ρ b.dst != ρ t`.
      simp only [liveSetInterferenceOkB, KBinop.toEvent, List.all_cons,
        Bool.and_eq_true, List.all_eq_true] at hhead
      -- hhead.1 = the wr-row : (b.dst==b.dst ↦ true) ∧ ∀ x ∈ lo, (if b.dst==x ...)
      have hrow := hhead.1.2 t ht
      -- hrow : if b.dst == t then true else ρ b.dst != ρ t  (= true)
      have hbt : (b.dst == t) = false := by
        rw [beq_eq_false_iff_ne]; exact fun h => htd h.symm
      rw [hbt] at hrow
      simp only [Bool.false_eq_true, if_false] at hrow
      have : ρ b.dst ≠ ρ t := by simpa [bne, beq_iff_eq] using hrow
      exact fun hc => this hc.symm

/-! ## 5. The capstone: a CHECKABLE Boolean hypothesis for the allocation theorem

Composing the generic bridge with the Phase-2 whole-body theorem
`runKernel_allocKernel_live` retires the per-kernel `native_decide`: the
hypothesis is now the **array-backed Boolean** `interferenceOkB` on the sinked
trace (which `liveOutsImpl` runs on the 107k body without stack overflow), plus
the cheap per-binop no-clobber `allBinopsNoClobberB`. No abstract
`InterferenceRespectedSeeded` proposition is required from the caller. -/

/-- **Boolean-hypothesis allocation correctness.** If the Phase-0 array checker
    accepts `ρ` on the sinked kernel trace (`interferenceOkB`) and the cheap
    per-binop no-clobber Boolean passes (`allBinopsNoClobberB`), then the
    allocated run agrees with the naive run through `ρ` on every output slot
    `L0`. `ρ` is **not** assumed injective. This is the scalable replacement for
    the per-kernel whole-body `native_decide`: both hypotheses are decidable
    Boolean checks that run on the compiled `liveOutsImpl` pass. -/
theorem runKernel_allocKernel_checked {w : Nat} (L0 : List Nat) (ρ : Nat → Nat)
    (k : Kernel)
    (hir : interferenceOkB (sinkedTrace L0 k) ρ = true)
    (hnc : allBinopsNoClobberB ρ k = true)
    (st' st : RegStore w)
    (hstart : AgreeOnLive ρ st' st (liveInSeeded L0 k)) :
    AgreeOnLive ρ (runKernel st' (allocKernel ρ k)) (runKernel st k) L0 :=
  runKernel_allocKernel_live L0 ρ k
    (interferenceSeeded_of_interferenceOkB L0 ρ k hir)
    (allBinopsNoClobber_of_boolB ρ k hnc) st' st hstart

/-- **Per-output corollary.** The checked allocation theorem read off at one
    output slot `s ∈ L0`: the allocated store at `ρ s` equals the naive store at
    `s`. The form the back-end's ABI epilogue consumes (read output `s` from its
    residence class `ρ s`). -/
theorem output_agree_of_checked {w : Nat} (L0 : List Nat) (ρ : Nat → Nat)
    (k : Kernel)
    (hir : interferenceOkB (sinkedTrace L0 k) ρ = true)
    (hnc : allBinopsNoClobberB ρ k = true)
    (st' st : RegStore w)
    (hstart : AgreeOnLive ρ st' st (liveInSeeded L0 k))
    (s : Nat) (hs : s ∈ L0) :
    (runKernel st' (allocKernel ρ k)) (ρ s) = (runKernel st k) s :=
  runKernel_allocKernel_checked L0 ρ k hir hnc st' st hstart s hs

/-! ## 6. Concrete demo: the MDS kernel via the array checker

A small sanity demo confirming the checked theorem fires on the concrete MDS
kernel through the *array-backed* `interferenceOkB` (a single `native_decide`
over the fixed 7-binop sinked trace — NOT a loop-running denotation fold). This
is the Phase-1/2 concrete case re-derived through the Phase-0 scalable checker,
demonstrating the same path the 107k body will take. -/

/-- The Phase-0 array checker accepts the MDS allocation on the sinked trace.
    A finite check over the fixed 7-binop kernel. -/
theorem mds4_interferenceOkB :
    interferenceOkB (sinkedTrace mds4Outputs mds4Kernel) mds4Rho = true := by
  native_decide

/-- **MDS outputs via the array checker.** The concrete MDS output equality, now
    discharged through the *generic* Phase-0→Phase-2 bridge (array-backed
    `interferenceOkB`), not the per-kernel seeded table. Subsumes
    `mds4Rho_outputs_eq_of_general`. -/
theorem mds4Rho_outputs_eq_checked {w : Nat} (st' st : RegStore w)
    (h0 : st' (mds4Rho 0) = st 0) (h1 : st' (mds4Rho 1) = st 1)
    (h2 : st' (mds4Rho 2) = st 2) (h3 : st' (mds4Rho 3) = st 3) :
    let stA := runKernel st' (allocKernel mds4Rho mds4Kernel)
    let stN := runKernel st mds4Kernel
    stA (mds4Rho 7) = stN 7 ∧ stA (mds4Rho 8) = stN 8 ∧
    stA (mds4Rho 9) = stN 9 ∧ stA (mds4Rho 10) = stN 10 := by
  have hstart : AgreeOnLive mds4Rho st' st (liveInSeeded mds4Outputs mds4Kernel) := by
    intro s hs
    rcases mds4_liveInSeeded s hs with h | h | h | h <;> subst h <;> assumption
  have hchecked := runKernel_allocKernel_checked mds4Outputs mds4Rho mds4Kernel
    mds4_interferenceOkB mds4_noClobberB st' st hstart
  simp only
  exact ⟨hchecked 7 (by simp [mds4Outputs]), hchecked 8 (by simp [mds4Outputs]),
    hchecked 9 (by simp [mds4Outputs]), hchecked 10 (by simp [mds4Outputs])⟩

end CatCrypt.Crypto.SecureCompilation.VIR.JasminRegAllocPhase3
