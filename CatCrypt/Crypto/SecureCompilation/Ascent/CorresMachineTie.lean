/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresGeneric
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresBridgeArithComplete

/-!
# `SimTie` — the cross-machine simulation, and the shape of the `jasmin ↔ runBlock` leg

The per-fragment middle ties (`CorresBridgeArith*`, `-Ctrl`, `-Mem`) each relate a
run of `semScalar` to a run of `runBlock`. `SimTie` is that relation stated once, as
a **cross-machine forward simulation**: two machines with steps `stepA`/`stepB`, a
state relation `R`, and a program on each side; from `R`-related states both advance
to `R`-related states.

`SimTie` composes (`simTie_seq`) under each machine's Kleisli-bind sequencing law —
the two laws already proved in `CorresGeneric` (`semScalar_seq_bind`,
`runBlockStep_append`). So a block or loop tie is `simTie_seq` folded over the
straight-line list, rather than a bespoke induction per fragment.

## The `jasmin ↔ runBlock` leg this is the shape of

`Com jasminDialect .denote` computes over **SSA values** (`BitVec w`, dataflow — no
machine state); `Com x86Dialect .denote` computes over a whole **`JState`** and
equals `runBlock` (`X86Dialect.lowerBlock_denote`). The leg missing from the
descent compiler's dialect chain — `jasminDialect.denote ↔ runBlock` — is therefore
a **register-allocation correctness** statement: the register-threaded machine
reproduces the SSA-value denotation. `LowCTToJInstrCT.lowerArith_denote` proves
exactly this at the arithmetic fragment (allocate via a `RegMap`, run, match the
value), so the middle ties are its LowCT-level instances. `SimTie` gives that leg
its compositional structure; closing it for the whole jasmin dialect (every op,
general allocation) is the descent compiler's open frontier.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT

/-- The cross-machine forward simulation: from `R`-related states `mA`/`mB`, the
    two machines advance (`stepA cA`/`stepB cB`) to states again related by `R`.
    Generic in both machines' states/programs and the relation. -/
def SimTie {MA MB CA CB : Type} (stepA : CA → MA → Option MA) (stepB : CB → MB → Option MB)
    (R : MA → MB → Prop) (cA : CA) (cB : CB) : Prop :=
  ∀ mA mB, R mA mB → ∃ mA' mB', stepA cA mA = some mA' ∧ stepB cB mB = some mB' ∧ R mA' mB'

/-- The empty programs (a no-op on each side) preserve `R`. `simpA`/`simpB` supply
    each machine's "skip runs to the same state" fact. -/
theorem simTie_skip {MA MB CA CB : Type} (stepA : CA → MA → Option MA)
    (stepB : CB → MB → Option MB) (R : MA → MB → Prop) (skipA : CA) (skipB : CB)
    (hA : ∀ m, stepA skipA m = some m) (hB : ∀ m, stepB skipB m = some m) :
    SimTie stepA stepB R skipA skipB :=
  fun mA mB hR => ⟨mA, mB, hA mA, hB mB, hR⟩

/-- **Cross-machine sequencing.** Under each machine's Kleisli-bind law, two
    `SimTie`s compose: the sequenced programs relate the same way. This is the one
    combinator a block/loop tie folds over. -/
theorem simTie_seq {MA MB CA CB : Type} (stepA : CA → MA → Option MA)
    (stepB : CB → MB → Option MB) (seqA : CA → CA → CA) (seqB : CB → CB → CB)
    (R : MA → MB → Prop)
    (hbindA : ∀ c₁ c₂ m, stepA (seqA c₁ c₂) m = (stepA c₁ m).bind (stepA c₂))
    (hbindB : ∀ c₁ c₂ m, stepB (seqB c₁ c₂) m = (stepB c₁ m).bind (stepB c₂))
    {cA₁ cA₂ : CA} {cB₁ cB₂ : CB}
    (h₁ : SimTie stepA stepB R cA₁ cB₁) (h₂ : SimTie stepA stepB R cA₂ cB₂) :
    SimTie stepA stepB R (seqA cA₁ cA₂) (seqB cB₁ cB₂) := by
  intro mA mB hR
  obtain ⟨midA, midB, hA₁, hB₁, hRmid⟩ := h₁ mA mB hR
  obtain ⟨mA', mB', hA₂, hB₂, hRfin⟩ := h₂ midA midB hRmid
  exact ⟨mA', mB', by rw [hbindA, hA₁, Option.bind_some, hA₂],
    by rw [hbindB, hB₁, Option.bind_some, hB₂], hRfin⟩

/-! ## The middle tie as a `SimTie` (arithmetic fragment) -/

/-- The middle-tie state relation: the scalar env agrees with the register view of
    the machine state on every non-temp name. -/
def midTieR (env : SEnvScalar) (st : JState 64) : Prop :=
  ∀ v, ¬ isTmpName v → env v = some ⟨.sword 64, st.regs v⟩

/-- A single arithmetic statement is a `SimTie` between `semScalar` and
    `runBlockStep`, via `arith_step_tie_gen`. -/
theorem simTie_arith (p : ArithSrc) (ha : ¬ isTmpName p.a) (hbt : ¬ isTmpName p.b)
    (hb : p.b ≠ p.dst) :
    SimTie semScalar runBlockStep midTieR (ArithSrc.toLowCT p) (lowerArith id p) := by
  intro env st hR
  obtain ⟨env1, hsem, hrel⟩ := arith_step_tie_gen p st env hR ha hbt hb
  exact ⟨env1, runBlock st (lowerArith id p), hsem, rfl, hrel⟩

/-- `RSkip` / the empty machine block is a `SimTie` (the block base case). -/
theorem simTie_skip_arith :
    SimTie semScalar runBlockStep midTieR .RSkip [] :=
  simTie_skip semScalar runBlockStep midTieR .RSkip []
    (fun _ => rfl) (fun _ => rfl)

/-- **The block-level middle tie via the combinator.** A straight-line arithmetic
    block is a `SimTie` by folding `simTie_seq` over the list — the compositional
    re-derivation of `arith_middle_tie_seq_nonTmp`, no bespoke induction. -/
theorem simTie_arith_seq (ps : List ArithSrc)
    (hwf : ∀ p ∈ ps, p.b ≠ p.dst)
    (hclean : ∀ p ∈ ps, ¬ isTmpName p.a ∧ ¬ isTmpName p.b) :
    SimTie semScalar runBlockStep midTieR
      (ArithSrc.seqToLowCT ps) (lowerSeq id ps) := by
  induction ps with
  | nil => exact simTie_skip_arith
  | cons p ps ih =>
    have hp := hclean p (List.mem_cons_self ..)
    have hstep : SimTie semScalar runBlockStep midTieR
        (ArithSrc.toLowCT p) (lowerArith id p) :=
      simTie_arith p hp.1 hp.2 (hwf p (List.mem_cons_self ..))
    have htail := ih (fun q hq => hwf q (List.mem_cons_of_mem p hq))
      (fun q hq => hclean q (List.mem_cons_of_mem p hq))
    have hseq := simTie_seq semScalar runBlockStep .RSeq (· ++ ·) midTieR
      (fun c₁ c₂ m => semScalar_seq_bind c₁ c₂ m) runBlockStep_append hstep htail
    simpa only [ArithSrc.seqToLowCT_cons, List.flatMap_cons, lowerSeq] using hseq

end CatCrypt.Crypto.SecureCompilation.Ascent
