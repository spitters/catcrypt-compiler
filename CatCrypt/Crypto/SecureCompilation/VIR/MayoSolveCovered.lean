/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenote
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenote
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenoteSeqExt
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenoteSeqExt

/-!
# MAYO-1 GF(16) linear solve whole-program denote through the covered `RSeq`-of-control fragment

The MAYO-1 `sample_solution` contract (MAYO-C `src/arithmetic.c`) is a **deep
multi-phase memory kernel**: build the augmented matrix `A : m × (k·o+1)` over
GF(16) (`x ← r`, then last column `A[i,·] ← y[i] − A[i]·r`), row-reduce it to
echelon form in constant time, then constant-time back-substitution into the
oil-variable vector `x`. Its top-level control is a *sequence of counted phases*:

```
copy (for i in 0..ko) ; lastcol (for i in 0..m) ; echelon (for pcol in 0..AC) ; backsub (for rr in 0..m)
```

Each phase is a **static-count** outer loop (the matrix dims `m = 78`, `k·o = 80`,
`AC = 81` are compile-time constants), so each phase is an `RFor`, and the four
phases are sequenced with `RSeq`. This is exactly the shape the canonical front
accepts after the `RSeq`-of-control increment: `translateDialectControl` closes
under `RSeq`-sequencing of control blocks, so the whole solve descends through the
canonical front and carries a **whole-program machine denote**.

This re-sources the solve from a high-level `LowCT` term
(`mayoSolveLowCT = RSeq copy (RSeq lastcol (RSeq echelon backsub))`) through the
**existing covered-fragment front** — no new front — and banks the whole-program
denote homomorphism, the same recipe as
`Fe25519ScalarmultCovered.fullScalarmultCovered_denote` and
`Shake256Covered.shake256Covered_denote`. It strengthens the hand-composed
`MAYO.SolveGf16FrontGen.WholeSolve` (a step-composition `ComL` schedule with no
whole-program machine denote) to a genuine high-level-source descent.

## Opaque leaves — the per-step GF(16) work, exactly the exemplar tier

Each per-iteration body is an **opaque leaf** (`RCall`), exactly as
`keccakf1600` / `x25519_ladder_iter` are opaque in the two exemplars. What is
banked here is the descent of the solve's **control structure** — the four
static-count phases sequenced — through the canonical front, with a whole-program
denote. The per-step GF(16) arithmetic (the carryless multiply, the CT pivot
masks) is the separate byte-KAT obligation (`mayo_compare`,
`make mayo-solve-emit-kat`), just as Keccak-f's permutation correctness is the
FIPS-202 KAT.

## The boundary — data-dependent inner sweeps stay inside the leaves

The **outer** phase loops are static-count (`ko`/`m`/`AC`), so `RFor` suffices —
no `RWhileNz` at the phase level. But each echelon step's *inner* sweeps
(`SolveGf16FrontGen` §8's `rc = up−lb+1`, `rc4 = ub−lb+1`, `rc6 = m−lb`) and each
back-substitution step's inner sweeps (`cc`, `ic2 = row`) have **runtime-computed
trip counts** — a per-outer-pass `f(pcol)` / `f(row)` count, *data-dependent but
public* (constant-time is preserved; the secret pivot row `prow` never indexes or
bounds anything, only feeds CT comparison masks). A runtime-count loop is an
`RWhileNz`/`forLoopNRt`, which lives OUTSIDE the static-count `RFor`+`RSeq`
covered fragment. Those inner sweeps are therefore kept **inside the opaque
per-step leaves** (`mayo_solve_ef_step`, `mayo_solve_backsub_step`), exactly as
Keccak-f's 24 rounds live inside `keccakf1600`. Opening a leaf to descend its full
body (rather than treat it opaque) is the `RWhileNz` data-dependent-count arm the
parallel work is building; it is not needed for the whole-program *control*
descent banked here.

Likewise the matrix cell access is at a *public* runtime index (`i·AC + j`,
derived from public counters) — the covered-fragment array boundary; kept inside
the leaves for this control-level descent.

## What is banked

* `mayoSolveLowCT` — the solve as `RSeq copy (RSeq lastcol (RSeq echelon backsub))`.
* `mayoSolve_coveredSeq : IsCoveredSCtlSeq mayoSolveLowCT` — the structural coverage
  proof (an `RSeq` spine of four covered `RFor` phases over opaque leaves).
* `mayoSolve_front_fires` — the covered front fires on the whole solve (`native_decide`).
* `mayoSolveCovered_denote` — **the deliverable**: the whole-program machine denote
  of the solve through the canonical front, via `transCtlSeq_denote_seq` and the
  `mayoSolve_front_eq` bridge (`transCtlSeq = translateDialectControl` on this
  `RSeq`-of-leaves term, via the nested `transCtlSeq_rseq_congr`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.MayoSolveCovered

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.Jasmin.LowCT (LowCT Located TowerType SExpr)

/-! ## 0. MAYO-1 solve parameters (the `solve_from_rustcmd.lean` schedule) -/

/-- Number of equations `m = 78` (echelon rows / back-substitution rows). -/
def pM : Nat := 78
/-- Oil-variable count `k·o = 80` (the `x ← r` copy length). -/
def pKO : Nat := 80
/-- Augmented column count `k·o + 1 = 81` (the echelon pivot-column sweep). -/
def pAC : Nat := 81

/-! ## 1. The high-level source: the solve as `copy ; lastcol ; echelon ; backsub` -/

/-- Tower type of a matrix/vector state bundle. All arrays (`A`, `y`, `r`, `x`,
    `P`, `P2`) are bundles of this placeholder type; the per-step GF(16) work is
    opaque, so the concrete cell layout is the leaves' KAT concern, not the
    control descent's. -/
def bundleTy : TowerType := .TBytes 200

/-- A located slot of a state-bundle tower type. -/
def loc (n : String) : Located := { locVar := n, locSrc := bundleTy }

/-- One copy iteration: `x[i] ← r[i]` — an opaque per-cell leaf threading `x`. -/
def copyStepBody : LowCT :=
  .RCall "mayo_solve_copy_step" (loc "x") [loc "x", loc "r"]

/-- **Phase 1a — the `x ← r` copy:** `RFor` over the oil variables (`0..ko`,
    static). A single `RFor`, so it lives in the denote-carrying covered fragment
    `IsCoveredSCtl`. -/
def copyLoop : LowCT :=
  .RFor "i" pKO copyStepBody

/-- One last-column iteration for row `i`: compute `A[i, ko] ← y[i] ^ (Σ_j
    A[i·AC+j]·r[j])` — an opaque leaf (the inner dot-accumulate is a static
    `0..ko` sweep, kept inside the leaf) threading `A`. -/
def lastColStepBody : LowCT :=
  .RCall "mayo_solve_lastcol_step" (loc "A") [loc "A", loc "y", loc "r"]

/-- **Phase 1b — the augmented last column:** `RFor` over the rows (`0..m`,
    static). -/
def lastColLoop : LowCT :=
  .RFor "i" pM lastColStepBody

/-- One echelon iteration for pivot column `pcol`: the whole constant-time
    echelon step (bounds from `pcol`, pivot search, invert, conditional
    write-back, eliminate-below) — an opaque leaf. Its *inner* row sweeps have
    runtime-computed (`f(pcol)`, public) trip counts (`RWhileNz`); those stay
    inside the leaf, exactly as Keccak-f's rounds stay inside `keccakf1600`. -/
def efStepBody : LowCT :=
  .RCall "mayo_solve_ef_step" (loc "A") [loc "A", loc "P", loc "P2"]

/-- **Phase 2 — echelon (row reduction):** `RFor` over the pivot columns
    (`0..AC`, static). -/
def echelonLoop : LowCT :=
  .RFor "pcol" pAC efStepBody

/-- One back-substitution iteration for descending row `rr`: sweep the columns and
    fold `A[·, last]` into `x` — an opaque leaf (its inner `cc`/`ic2` sweeps are
    runtime-count, kept inside the leaf) threading `x`. -/
def backsubStepBody : LowCT :=
  .RCall "mayo_solve_backsub_step" (loc "x") [loc "A", loc "x"]

/-- **Phase 3 — back-substitution:** `RFor` over the rows (`0..m`, static). -/
def backsubLoop : LowCT :=
  .RFor "rr" pM backsubStepBody

/-- **The full MAYO-1 GF(16) solve as a multi-phase kernel:** the copy, last-column,
    echelon, and back-substitution phases *sequenced* — the top-level
    `RSeq (RFor …) (RSeq (RFor …) (RSeq (RFor …) (RFor …)))` shape. -/
def mayoSolveLowCT : LowCT :=
  .RSeq copyLoop (.RSeq lastColLoop (.RSeq echelonLoop backsubLoop))

/-! ## 2. Coverage — the load-bearing structural proofs -/

/-- The copy-step body is straight-line covered. -/
theorem copyStepBody_coveredS : IsCoveredS copyStepBody :=
  .rCall "mayo_solve_copy_step" (loc "x") [loc "x", loc "r"]

/-- The copy loop is Stage-2 covered (`IsCoveredSCtl`): a bounded `RFor` over the
    straight-line copy step. -/
theorem copyLoop_covered : IsCoveredSCtl copyLoop :=
  .rFor (.ofStraight copyStepBody_coveredS)

/-- The last-column-step body is straight-line covered. -/
theorem lastColStepBody_coveredS : IsCoveredS lastColStepBody :=
  .rCall "mayo_solve_lastcol_step" (loc "A") [loc "A", loc "y", loc "r"]

/-- The last-column loop is Stage-2 covered (`IsCoveredSCtl`). -/
theorem lastColLoop_covered : IsCoveredSCtl lastColLoop :=
  .rFor (.ofStraight lastColStepBody_coveredS)

/-- The echelon-step body is straight-line covered. -/
theorem efStepBody_coveredS : IsCoveredS efStepBody :=
  .rCall "mayo_solve_ef_step" (loc "A") [loc "A", loc "P", loc "P2"]

/-- The echelon loop is Stage-2 covered (`IsCoveredSCtl`). -/
theorem echelonLoop_covered : IsCoveredSCtl echelonLoop :=
  .rFor (.ofStraight efStepBody_coveredS)

/-- The back-substitution-step body is straight-line covered. -/
theorem backsubStepBody_coveredS : IsCoveredS backsubStepBody :=
  .rCall "mayo_solve_backsub_step" (loc "x") [loc "A", loc "x"]

/-- The back-substitution loop is Stage-2 covered (`IsCoveredSCtl`). -/
theorem backsubLoop_covered : IsCoveredSCtl backsubLoop :=
  .rFor (.ofStraight backsubStepBody_coveredS)

/-- **The full MAYO-1 solve is control-sequencing covered** (`IsCoveredSCtlSeq`):
    the four counted phases sequenced. Not expressible in `IsCoveredSCtl` (which
    has no `RSeq`-over-control) — this is exactly the `RSeq`-of-control increment,
    here a four-phase spine (deeper than the exemplars' two/three phases). -/
theorem mayoSolve_coveredSeq : IsCoveredSCtlSeq mayoSolveLowCT :=
  .rSeq (.ofCtl copyLoop_covered)
    (.rSeq (.ofCtl lastColLoop_covered)
      (.rSeq (.ofCtl echelonLoop_covered) (.ofCtl backsubLoop_covered)))

/-! ## 3. Concrete argument context — the front fires -/

/-- Six-argument context: the `A`, `y`, `r`, `x`, `P`, `P2` bundles. -/
def solveArgCtx : Ctx :=
  [encodeTy bundleTy, encodeTy bundleTy, encodeTy bundleTy,
   encodeTy bundleTy, encodeTy bundleTy, encodeTy bundleTy]

/-- Name resolver binding `A`/`y`/`r`/`x`/`P`/`P2` to the six bundle arguments. -/
def solveArgVM : VarMap solveArgCtx where
  lookup := fun s =>
    if s = "A" then some ⟨encodeTy bundleTy, .here⟩
    else if s = "y" then some ⟨encodeTy bundleTy, .there .here⟩
    else if s = "r" then some ⟨encodeTy bundleTy, .there (.there .here)⟩
    else if s = "x" then some ⟨encodeTy bundleTy, .there (.there (.there .here))⟩
    else if s = "P" then some ⟨encodeTy bundleTy, .there (.there (.there (.there .here)))⟩
    else if s = "P2" then some ⟨encodeTy bundleTy, .there (.there (.there (.there (.there .here))))⟩
    else none

/-- **The covered front fires on the whole MAYO-1 solve.** The four bounded `RFor`
    phases unroll `CProg`-free through `loopRForD`, each opaque per-step leaf
    resolves its bundle arguments, the `RSeq` spine composes the phase prefixes,
    and the top-level terminator closes. -/
theorem mayoSolve_front_fires :
    (translateDialectControlTop solveArgVM mayoSolveLowCT).isSome := by
  native_decide

/-! ## 4. `transCtlSeq` coincides with the canonical front on this term

The control-sequencing front `transCtlSeq` folds `translateDialectControl` along
the `RSeq` spine with `ComCont.comp`; the canonical `translateDialectControl` now
does the *same* (its `RSeq` arm recurses into itself). On leaves (`RFor`)
`transCtlSeq` delegates to `translateDialectControl` through its wildcard. So on
this pure `RSeq`-of-leaves term the two fronts coincide, letting the
canonical-front translation hypothesis feed the control-sequencing homomorphism
`transCtlSeq_denote_seq` directly. -/

/-- `RSeq` congruence for the two fronts: if both children agree pointwise, the
    sequence agrees. Both fronts share the identical `RSeq` arm (recurse into
    self, compose with `ComCont.comp`), so this is a one-layer unfold. -/
theorem transCtlSeq_rseq_congr {c₁ c₂ : LowCT}
    (h1 : ∀ {Δ : Ctx} (w : VarMap Δ), transCtlSeq w c₁ = translateDialectControl w c₁)
    (h2 : ∀ {Δ : Ctx} (w : VarMap Δ), transCtlSeq w c₂ = translateDialectControl w c₂)
    {Γ : Ctx} (vm : VarMap Γ) :
    transCtlSeq vm (.RSeq c₁ c₂) = translateDialectControl vm (.RSeq c₁ c₂) := by
  simp only [transCtlSeq, translateDialectControl, h1, h2]
  rfl

/-- On the innermost `RSeq echelonLoop backsubLoop` (two `RFor` leaves),
    `transCtlSeq` coincides with the canonical front. -/
theorem inner1_front_eq {Γ : Ctx} (vm : VarMap Γ) :
    transCtlSeq vm (.RSeq echelonLoop backsubLoop)
      = translateDialectControl vm (.RSeq echelonLoop backsubLoop) :=
  transCtlSeq_rseq_congr (fun _ => rfl) (fun _ => rfl) vm

/-- On `RSeq lastColLoop (RSeq echelonLoop backsubLoop)`, `transCtlSeq` coincides
    with the canonical front (leaf `RFor` + the inner sequence). -/
theorem inner2_front_eq {Γ : Ctx} (vm : VarMap Γ) :
    transCtlSeq vm (.RSeq lastColLoop (.RSeq echelonLoop backsubLoop))
      = translateDialectControl vm (.RSeq lastColLoop (.RSeq echelonLoop backsubLoop)) :=
  transCtlSeq_rseq_congr (fun _ => rfl) (fun _ => inner1_front_eq _) vm

/-- **The full solve front-agreement.** `transCtlSeq` coincides with the canonical
    `translateDialectControl` on `mayoSolveLowCT`: the outer `RSeq` uses the
    congruence with the leaf `copyLoop` (`RFor`, agrees by the `transCtlSeq`
    wildcard) and the inner two-phase sequence (`inner2_front_eq`). -/
theorem mayoSolve_front_eq {Γ : Ctx} (vm : VarMap Γ) :
    transCtlSeq vm mayoSolveLowCT = translateDialectControl vm mayoSolveLowCT :=
  transCtlSeq_rseq_congr (fun _ => rfl) (fun _ => inner2_front_eq _) vm

/-! ## 5. THE DELIVERABLE — the whole-program denote homomorphism

For the MAYO-1 solve, the descended `Com catCryptDialect` prefix denotes exactly
the kernel's `semScalar` waist — the four-phase whole-program denote through the
canonical front, banked via the control-sequencing homomorphism
`transCtlSeq_denote_seq` (which equals `translateDialectControl` on this
`RSeq`-of-leaves term by `mayoSolve_front_eq`, so the canonical-front translation
hypothesis feeds it directly). The per-step GF(16) work (and each step's
data-dependent inner sweeps) are opaque leaves; their correctness is the separate
byte-KAT obligation. -/

/-- **Whole-program machine denote of the MAYO-1 GF(16) solve** (copy `;` lastcol
    `;` echelon `;` backsub). For any context/valuation/env consistent triple on
    which the canonical front fires and the `semScalar` waist succeeds, the
    descended dialect-`Com` prefix denotes exactly the solve's `semScalar`
    semantics (per-tail continuation). -/
theorem mayoSolveCovered_denote :
    ∀ {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env env' : SEnvScalar) (o : DTransOut Γ),
      ConsistentS vm V env →
      translateDialectControl vm mayoSolveLowCT = some o →
      semScalar mayoSolveLowCT env = some env' →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentS o.vm V' env' ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com : Com catCryptDialect Γ t,
            o.cont tail = some com ∧ com.denote V = tail.denote V' := by
  intro Γ vm V env env' o hc htr hsem
  rw [← mayoSolve_front_eq vm] at htr
  exact transCtlSeq_denote_seq mayoSolve_coveredSeq vm V env env' o hc htr hsem

/-! ## 6. Axiom audit -/

#print axioms mayoSolve_coveredSeq
#print axioms mayoSolve_front_fires
#print axioms mayoSolve_front_eq
#print axioms mayoSolveCovered_denote

end CatCrypt.Crypto.SecureCompilation.VIR.MayoSolveCovered
