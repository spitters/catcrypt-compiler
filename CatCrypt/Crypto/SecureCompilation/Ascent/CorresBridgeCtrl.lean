/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Ascent.CorresBridgeArithComplete
import CatCrypt.Crypto.SecureCompilation.X86Backend.LoopUnroll

/-!
# The control-fragment middle tie for a bounded for-loop (`semScalar` ↔ `runBlock`)

`CorresBridgeArith` / `CorresBridgeArithComplete` tie the scalar `semScalar`
machine to the flag-carrying `runBlock` machine for a single `ArithSrc`
(`arith_middle_tie_at_dst`) and for a straight-line block of them
(`arith_middle_tie_seq_nonTmp`).  This module lifts that tie one control level up
— to a **bounded for-loop** `RFor x N body`, the loop analogue of the arithmetic
tie.

The two machines meet as follows.

* **Source.** `semScalar (RFor x N body)` is the structural `Nat`-recursion
  `semRForD (fun e => semScalar body e) x N` (`TranslateDialectScalarDenote`): it
  runs the body `N` times, and **before each trip binds the counter `x` to the
  trip index** (`envPre.upd x n`), peeling the LAST trip first.
* **Machine.** `runBlock st (unrollBounded N bodyM)` runs the fully-unrolled
  `N`-fold straight-line block (`LoopUnroll.unrollBounded`).  `unrollBounded`
  prepends one body per step (`unrollBounded_succ`); the last-peel orientation the
  source uses is recovered by `unrollBounded_succ_right`
  (`unrollBounded (n+1) = unrollBounded n ++ body`), so both machines peel their
  last trip in lock-step.

## The per-iteration body tie is the parameter

The loop tie is **body-agnostic**: it is parameterised over the body's own
per-iteration middle tie (`hbody`).  A per-iteration tie relates, at trip index
`n`, the source running `body` from the counter-bound env `env.upd x n` with the
machine running `bodyM` from a state agreeing with `env` on non-temp names, and
re-establishes that agreement on the post-states.  `for_middle_tie_gen` threads
`hbody` through the `N`-fold fold by induction on `N`.

## The loop variable is the subtle axis

The source binds `x := n` before each trip; the machine unroll never writes `x`.
So a **non-temp** loop counter is a slot where the two machines genuinely
disagree (the source overwrites it, the machine leaves it stale) unless the body
itself maintains it.  `for_middle_tie_arith` instantiates the abstract tie at a
straight-line arithmetic body under the honest side-condition **`isTmpName x`**:
when the counter lives in the reserved `__sx` temp namespace it is quotiented out
of the observed non-temp fibre (`nonTmpAgree_upd_tmp`), so the counter bind is
invisible to the readout and `arith_seq_tie_gen` supplies the per-iteration tie
directly.  For a non-temp counter the mismatch on `x` is a real semantic fact,
not a proof artefact — it is recorded in the `hbody` hypothesis rather than
papered over.

## Trust story

No new axioms beyond the arithmetic tie and the unroll bridge
(`[propext, Classical.choice, Quot.sound]`).  `unrollBounded_succ_right` is a
`List`-append induction; `for_middle_tie_gen` is a `Nat` induction peeling one
trip per step; `for_middle_tie_arith` is its instantiation via
`arith_seq_tie_gen`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoopUnroll

/-! ## The last-peel orientation of the unroller -/

/-- **Right (last-trip) peel of `unrollBounded`.**  `unrollBounded` prepends one
    body per step (`unrollBounded_succ : unrollBounded (k+1) = body ++ …`); this
    is the dual, appending the last copy: `unrollBounded (n+1) body =
    unrollBounded n body ++ body`.  It re-orients the machine unroll to match the
    source `semRForD`, which peels the LAST trip first.  By induction on `n`,
    reassociating the `List` append. -/
theorem unrollBounded_succ_right {w : Nat} (n : Nat) (body : List (JInstr w)) :
    unrollBounded (n + 1) body = unrollBounded n body ++ body := by
  induction n with
  | zero => simp [unrollBounded]
  | succ k ih =>
      calc unrollBounded (k + 2) body
          = body ++ unrollBounded (k + 1) body := by rw [unrollBounded_succ]
        _ = body ++ (unrollBounded k body ++ body) := by rw [ih]
        _ = (body ++ unrollBounded k body) ++ body := by rw [List.append_assoc]
        _ = unrollBounded (k + 1) body ++ body := by rw [unrollBounded_succ]

/-! ## The non-temp agreement invariant threaded through the loop -/

/-- The invariant the loop tie threads: the scalar env `env` agrees with the
    machine register file `st.regs` at the uniform word type on every non-temp
    name — the fresh `__sx` temporaries (which have no machine counterpart) are
    the only slots the two may disagree on.  Definitionally `env v = regEnv st v`
    on non-temp `v`; stated in the unfolded `some ⟨.sword 64, …⟩` form to line up
    with `arith_seq_tie_gen`'s agreement hypothesis. -/
def nonTmpAgree (env : SEnvScalar) (st : JState 64) : Prop :=
  ∀ v, ¬ isTmpName v → env v = some ⟨.sword 64, st.regs v⟩

/-- Binding a fresh (temp-namespace) name leaves the non-temp agreement intact:
    updating `env` at a name `x` with `isTmpName x` changes only a temp slot,
    which the readout ignores. -/
theorem nonTmpAgree_upd_tmp (env : SEnvScalar) (st : JState 64) (x : String)
    (hx : isTmpName x) (val : BitVec 64) (hag : nonTmpAgree env st) :
    nonTmpAgree (env.upd x (t := .sword 64) val) st := by
  intro v hv
  have hne : v ≠ x := fun h => hv (by rw [h]; exact hx)
  simp only [SEnvScalar.upd, if_neg hne]
  exact hag v hv

/-! ## The abstract bounded-loop middle tie -/

/-- **The bounded for-loop middle tie (body-agnostic).**  Given the body's
    per-iteration middle tie `hbody` — at every trip index `n`, from any env
    agreeing with a machine state on non-temp names, running the source body from
    the counter-bound env `env.upd x n` succeeds and re-establishes the non-temp
    agreement against the machine body `runBlock stM bodyM` — the whole bounded
    loop ties: `semScalar (RFor x N body)` succeeds on any starting env agreeing
    with `st`, and its result agrees with `runBlock st (unrollBounded N bodyM)` on
    every non-temp name.

    Induction on `N`.  Base (`N = 0`): both machines are the identity.  Step
    (`N = n+1`): the induction hypothesis runs the first `n` trips
    (`semRForD`'s recursive prefix ↔ `unrollBounded n`); `hbody` runs the last
    trip (`semRForD`'s counter-bound tail ↔ the trailing body copy exposed by
    `unrollBounded_succ_right` + `runBlock_append`).  The loop analogue of
    `arith_middle_tie_seq_nonTmp`. -/
theorem for_middle_tie_gen (x : String) (bodyS : LowCT) (bodyM : List (JInstr 64))
    (hbody : ∀ (n : Nat) (env : SEnvScalar) (stM : JState 64),
        nonTmpAgree env stM →
        ∃ env1, semScalar bodyS (env.upd x (t := .sword 64) (BitVec.ofNat 64 n)) = some env1
          ∧ nonTmpAgree env1 (runBlock stM bodyM)) :
    ∀ (N : Nat) (st : JState 64) (env : SEnvScalar), nonTmpAgree env st →
      ∃ env', semScalar (.RFor x N bodyS) env = some env'
        ∧ nonTmpAgree env' (runBlock st (unrollBounded N bodyM)) := by
  intro N
  induction N with
  | zero =>
      intro st env hag
      exact ⟨env, rfl, hag⟩
  | succ n ih =>
      intro st env hag
      obtain ⟨envPre, hPre, hagPre⟩ := ih st env hag
      have hPre' : semRForD (fun e => semScalar bodyS e) x n env = some envPre := hPre
      obtain ⟨env1, hb1, hag1⟩ :=
        hbody n envPre (runBlock st (unrollBounded n bodyM)) hagPre
      refine ⟨env1, ?_, ?_⟩
      · show semRForD (fun e => semScalar bodyS e) x (n + 1) env = some env1
        simp only [semRForD, hPre', hb1]
      · rw [unrollBounded_succ_right, runBlock_append]
        exact hag1

/-! ## Instantiation at a straight-line arithmetic body -/

/-- **The bounded for-loop tie at an arithmetic body.**  For a source-clean,
    well-formed straight-line arithmetic block `ps : List ArithSrc` used as the
    loop body, with the loop counter `x` a fresh temp (`isTmpName x`), the
    bounded loop `RFor x N (seqToLowCT ps)` ties to the unrolled machine block
    `unrollBounded N (lowerSeq id ps)` on every non-temp name.

    The per-iteration body tie is discharged by `arith_seq_tie_gen`: the counter
    bind `x := n` lands on a temp slot (`nonTmpAgree_upd_tmp`), so it preserves
    the non-temp agreement the block tie consumes, and the block tie's output
    (`regEnv (runBlock …)`, definitionally `some ⟨.sword 64, …⟩`) is exactly the
    non-temp agreement on the post-state.  Instantiates `for_middle_tie_gen`. -/
theorem for_middle_tie_arith (x : String) (ps : List ArithSrc)
    (hx : isTmpName x)
    (hwf : ∀ p ∈ ps, p.b ≠ p.dst)
    (hclean : ∀ p ∈ ps, ¬ isTmpName p.a ∧ ¬ isTmpName p.b) :
    ∀ (N : Nat) (st : JState 64) (env : SEnvScalar), nonTmpAgree env st →
      ∃ env', semScalar (.RFor x N (ArithSrc.seqToLowCT ps)) env = some env'
        ∧ nonTmpAgree env' (runBlock st (unrollBounded N (lowerSeq id ps))) :=
  for_middle_tie_gen x (ArithSrc.seqToLowCT ps) (lowerSeq id ps)
    (by
      intro n env stM hag
      obtain ⟨env1, hsem, hro⟩ :=
        arith_seq_tie_gen ps hwf hclean stM
          (env.upd x (t := .sword 64) (BitVec.ofNat 64 n))
          (nonTmpAgree_upd_tmp env stM x hx _ hag)
      exact ⟨env1, hsem, fun v hv => hro v hv⟩)

end CatCrypt.Crypto.SecureCompilation.Ascent
