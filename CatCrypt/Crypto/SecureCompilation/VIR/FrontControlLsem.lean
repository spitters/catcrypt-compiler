/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLoop
public import CatCrypt.Crypto.Jasmin.LowCT
public import CatCrypt.Crypto.Jasmin.LowCTCTAnalysis

/-!
# Tying the `LowCT` FRONT control flow to the emitted control flow + labeled `lsem`

`JasminLsemLabeled.lean` defines the labeled, program-indexed,
fuel-bounded linear semantics (`lsemFuel`/`evalInstrP`/`evalJump`/`findLabel`,
with the `Lgoto`/`Lcond`/`Llabel` arms). `JasminLsemLoop.lean` gives
the *counted-loop* program-level `lsem` simulation: the real emitted loop
form `loopLR` (= `LprogControlFlow.loopLcmd` modulo the dropped flag-`CMP`,
`loopLR_eq_loopLcmd_dropCmp`) runs in `n`-fold lockstep with a per-iteration body
transformer `bodyStep`, with a public trip count, and its leak is
state-independent (constant-time).

This module ties the **`LowCT` FRONT** control-flow
constructs — `RFor`/`RWhileNz` (the counted loops) and `RIfNz` (the branch) — to
the emitted control flow and the labeled `lsem`.

## What the front constructs mean (`Jasmin/LowCT.lean`, `RustExec`)

The front is `LowCT` over `RustState`, with big-step semantics `RustExec`:

* `RFor x n body` — runs `body` `n` times, setting the scalar `x := 0,1,…,n-1`
  before each iteration (`RustExec.forZero`/`forSucc`). A *static* trip count `n`;
  the loop counter `x` is structurally public (it ranges over `0..n`, public
  literals). This is exactly the data-independent loop the CT analysis
  (`LowCTCTAnalysis.cmdCT (.RFor …)`, no guard) accepts.
* `RWhileNz x body` — runs `body` while the public scalar `x ≠ 0`
  (`RustExec.whileFalse`/`whileTrue`). CT requires `lt x = .Public`
  (`cmdCT_RWhileNz`) — a secret loop guard leaks the iteration count and is
  not CT.
* `RIfNz x ct cf` — branches on the scalar `x`: nonzero ⇒ `ct`, zero ⇒ `cf`
  (`RustExec.ifTrue`/`ifFalse`). CT requires `lt x = .Public` (`cmdCT_RIfNz`) — a
  secret-dependent branch is the canonical CT leak.

## Fidelity: route through the REAL emitted forms, do not reconstruct

* **Counted loops** — the emitted backend form is `loopLR` / `loopProg`
  (`JasminLsemLoop`), the `loopLcmd` shape (`loopLR_eq_loopLcmd_dropCmp`) that
  `LprogControlFlow.cforToLcmd` produces from a `JForProg`
  (`cforToLcmd_eq_loopLcmd`). We **reuse `loop_lsem_correct` /
  `loop_lsem_correct_and_robust` unchanged** — the program-level `lsem` run is the
  real `loopLR` driven by `lsemFuel`. The front tie is the structural
  correspondence: the front loop's `RustExec` post-state is the *same* `n`-fold
  body fold the `lsem` halt data is (the per-iteration body edge — one front
  `RustExec` body run = one `lsem` `bodyStep` under the state encoding — is a
  *named hypothesis* `FrontLoopEncodes`, exactly as `LoopBodySpec.run` and
  `JForProgCT.StepAgrees` carry the single-iteration body edge, never a `sorry`).
  The public trip count is `LoopTerminatesIn` + the front static `n`.

* **Branch** — the emitted form is the labeled `Lcond`-branch
  `ifLR cond Lthen Lend cf ct` run by **`evalInstrP`/`lsemFuel`** (the real
  `Lcond` arm: nonzero scrutinee ⇒ `evalJump` to the taken label, zero ⇒ fall
  through). The `Lcond` reads the SAME scrutinee register the front `RIfNz` tests;
  its leak is the constant `LLeak.branch` (`linstrLeak (.Lcond …) = [.branch]`) —
  state-independent given a public scrutinee, exactly `cmdCT_RIfNz`'s requirement.

## Public-control-flow CT hypotheses (stated, not hidden)

* Loop: `LoopTerminatesIn spec sb c` — the back-edge counter `"NZ"` is the public
  static trip count (vartime policy). Note: a secret trip count is not
  CT.
* Branch: `lt cond = .Public` — `RIfNz`'s scrutinee must be public-classified
  (`cmdCT_RIfNz`). A secret-dependent branch is not CT, and
  the `Lcond`'s `branch` leak would then depend on a secret.

**0 sorries; axioms ⊆ {propext, Classical.choice, Quot.sound}; no
`jasminc_preserves_ct`, no `JasminIRToX86` edge.**
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.FrontControlLsem

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLoop

/-! ## 1. The front counted loop's `RustExec` denotation as an `n`-fold fold

`RFor x n body` runs `body` `n` times, setting the scalar `x := i` before
iteration `i`. We capture one iteration's *effect on the front state* by a
per-iteration transformer `frontStep : Nat → RustState → RustState` (the named
body edge: `frontStep i rs` is the post-state of running `body` from
`rsSetScalar rs x i`). The whole loop's post-state is then the `n`-fold fold of
`frontStep` over `0..n` — exactly the shape `JForProg.denote` / `loopRun` (`JasminLsemLoop`)
computes, and the shape the `lsem` halt data has. -/

/-- The front loop's `n`-fold post-state: fold the per-iteration front transformer
    `frontStep` over `List.range n` from `rs`. The structural analogue of
    `JForProgCT.loopRun` / `reentry`-iterate, at the *front* (`RustState`)
    level. -/
def frontForRun (frontStep : Nat → RustState → RustState) (n : Nat)
    (rs : RustState) : RustState :=
  (List.range n).foldl (fun acc i => frontStep i acc) rs

@[simp] theorem frontForRun_zero (frontStep : Nat → RustState → RustState)
    (rs : RustState) : frontForRun frontStep 0 rs = rs := rfl

/-- One more iteration: `frontForRun … (n+1)` applies one extra `frontStep n`
    *after* the `n`-fold run. The per-iteration recurrence (the `List.range_succ`
    fold-unfolding), matching `RustExec.forSucc`'s shape. -/
theorem frontForRun_succ (frontStep : Nat → RustState → RustState) (n : Nat)
    (rs : RustState) :
    frontForRun frontStep (n + 1) rs
      = frontStep n (frontForRun frontStep n rs) := by
  unfold frontForRun
  rw [List.range_succ, List.foldl_append]
  rfl

/-- **The front `RFor`'s `RustExec` denotation is the `n`-fold `frontStep` fold.**
    Given the per-iteration body edge `hbody` — running `body` from
    `rsSetScalar rs x i` lands in `frontStep i rs` (the named single-iteration
    front edge, the front analogue of `LoopBodySpec.run` / `StepAgrees`,
    NOT a `sorry`) — the big-step `RustExec` of `RFor x n body` reaches exactly
    `frontForRun frontStep n rs`. Proof by induction on `n` via the `forZero` /
    `forSucc` rules. -/
theorem rustExec_rfor_frontForRun {N : Nat} {leafSpec : LeafSpec}
    (x : String) (body : LowCT) (frontStep : Nat → RustState → RustState)
    (hbody : ∀ (i : Nat) (rs : RustState),
        RustExec N leafSpec body (rsSetScalar rs x i) (frontStep i rs)) :
    ∀ (n : Nat) (rs : RustState),
      RustExec N leafSpec (.RFor x n body) rs (frontForRun frontStep n rs) := by
  intro n
  induction n with
  | zero => intro rs; simpa using RustExec.forZero (N := N) (leafSpec := leafSpec) x body rs
  | succ k ih =>
      intro rs
      rw [frontForRun_succ]
      exact RustExec.forSucc x k body rs (frontForRun frontStep k rs)
        (frontStep k (frontForRun frontStep k rs))
        (ih rs) (hbody k (frontForRun frontStep k rs))

/-! ## 2. The state encoding tying the front fold to the `lsem` body fold

The front loop runs over `RustState`; the emitted `loopLR` runs over `Lstate w`.
A `FrontLoopEncodes` packages the encoding `enc : RustState → Lstate w` together
with the single-iteration *commutation* edge: encoding the front post-state of one
iteration equals one `lsem` `bodyStep` of the encoded pre-state. This is the
front-to-`lsem` per-iteration body edge — the named hypothesis the whole-loop tie
factors through (exactly `LoopBodySpec.run` discipline). -/

/-- The encoding tie between the front per-iteration transformer `frontStep` and
    the `lsem` loop simulation (`JasminLsemLoop`). `enc` maps a front `RustState` to an `lsem`
    `Lstate`; `comm` is the single-iteration commuting square against the
    `reentry` recurrence — encoding one front iteration equals one `lsem`
    `bodyStep` re-pinned to the body-start pc `1` (exactly how `reentry (k+1)`
    advances). The per-iteration body edge — a named hypothesis, never a `sorry`.
    The loop counter `i` is the public `0..n` index; `bodyStep` reads the public
    back-edge counter, so the encoded step is `i`-independent. -/
structure FrontLoopEncodes {w : Nat} {body : List LinstrR}
    (spec : LoopBodySpec w body) (frontStep : Nat → RustState → RustState) where
  /-- Encode a front `RustState` into the `lsem` `Lstate`. -/
  enc : RustState → Lstate w
  /-- One front iteration, encoded, equals one `lsem` `bodyStep` re-pinned to the
      body-start pc `1` — the `reentry`-recurrence step (`JasminLsemLoop`). -/
  comm : ∀ (i : Nat) (rs : RustState),
      enc (frontStep i rs) = { spec.bodyStep (enc rs) with lpc := 1 }

/-- **The encoding lands on `reentry` data.** If the encoded front start
    `enc rs` is the loop start data `{ sb with lpc := 1 }`, then encoding the
    front loop's `k`-fold post-state equals the reentry data after `k` body runs
    (`(reentry spec sb k).base`). The structural lift of the single-iteration
    `comm` to the whole loop, by induction on `k` against `reentry_succ_data`. -/
theorem enc_frontForRun_eq_reentry {w : Nat} {body : List LinstrR}
    {spec : LoopBodySpec w body} {frontStep : Nat → RustState → RustState}
    (E : FrontLoopEncodes spec frontStep) (sb : Lstate w) (rs : RustState)
    (hstart : E.enc rs = { sb with lpc := 1 }) (k : Nat) :
    E.enc (frontForRun frontStep k rs) = (reentry spec sb k).base := by
  induction k with
  | zero => simpa using! hstart
  | succ m ih =>
      rw [frontForRun_succ, E.comm, ih, reentry_succ_data]

/-! ## 4. Capstone (loop): the front `RFor`'s lsem run = its `RustExec` denotation
+ constant-time

We combine three pieces — each the REAL artifact, none reconstructed:

* `rustExec_rfor_frontForRun` (§1): the front `RFor x (c+1) body`'s big-step
  `RustExec` post-state is the `(c+1)`-fold `frontStep` fold
  `frontForRun frontStep (c+1) rs`;
* `enc_frontForRun_eq_reentry` (§3): that front post-state, encoded, is the
  reentry data `(reentry spec sb (c+1)).base` — i.e. on lvm/lmem, the `lsem` halt
  data `spec.bodyStep ((reentry spec sb c).base)` (they differ only by the loop
  re-pin `lpc := 1` vs the halt `lpc := 2 + |body|`);
* `loop_lsem_correct` (`JasminLsemLoop`): the **real emitted loop** `loopProg = loopLR`
  (`loopLcmd` modulo the dropped flag-`CMP`, `loopLR_eq_loopLcmd_dropCmp`; the
  `cforToLcmd` image, `cforToLcmd_eq_loopLcmd`) runs in `lsemFuel` to that halt
  data over the public trip count `c+1`.

`LoopTerminatesIn spec sb c` is the **public-trip-count** hypothesis (stated, not
hidden): the back-edge counter `"NZ"` is the public static `c+1` (vartime
policy). -/

/-- **`front_loop_lsem_correct`.** For a front counted loop `RFor x (c+1) body`
    with per-iteration front edge `frontStep` (`hbody`) encoded into the lsem loop
    simulation (`E : FrontLoopEncodes spec frontStep`, starting at the loop entry
    data `enc rs = { sb with lpc := 1 }`), over a **public trip count** `c+1`
    (`hterm : LoopTerminatesIn spec sb c`):

    the program-level `lsemFuel` trace of the **real emitted loop** `loopProg`
    (the `loopLR`/`loopLcmd` shape) from the loop entry halts at the `lsem` data
    whose lvm/lmem is the encoding of the front loop's `RustExec` denotation
    `frontForRun frontStep (c+1) rs` — i.e. *the emitted loop computes the front
    loop's source meaning*. The two `lsem` states differ only by the loop re-pin
    `lpc := 1` (encoded front) vs the post-loop halt `lpc := 2 + |body|`, so we
    state the agreement on the observable data (`lvm`, `lmem`).

    No `JasminIRToX86` edge, no `jasminc_preserves_ct`. -/
theorem front_loop_lsem_correct {N : Nat} {leafSpec : LeafSpec}
    (x : String) (body : LowCT) (frontStep : Nat → RustState → RustState)
    (hbody : ∀ (i : Nat) (rs : RustState),
        RustExec N leafSpec body (rsSetScalar rs x i) (frontStep i rs))
    (fn : String) {w : Nat} (top : LLabel) {lbody : List LinstrR}
    (spec : LoopBodySpec w lbody) (sb : Lstate w) (c : Nat)
    (hterm : LoopTerminatesIn spec sb c)
    (E : FrontLoopEncodes spec frontStep) (rs : RustState)
    (hstart : E.enc rs = { sb with lpc := 1 }) :
    -- (front denotation) the front `RFor`'s `RustExec` post-state
    RustExec N leafSpec (.RFor x (c + 1) body) rs (frontForRun frontStep (c + 1) rs)
    ∧
    -- (emitted lsem run) the real emitted loop halts at the lsem data whose
    -- lvm/lmem encodes that front post-state.
    (∃ t : Lstate w,
        lsemFuel (loopProg fn top lbody) ((c + 1) * (lbody.length + 1) + 1)
            { base := { sb with lpc := 0 }, lfn := fn }
          = some { base := t, lfn := fn }
      ∧ t.lvm = (E.enc (frontForRun frontStep (c + 1) rs)).lvm
      ∧ t.lmem = (E.enc (frontForRun frontStep (c + 1) rs)).lmem) := by
  refine ⟨rustExec_rfor_frontForRun x body frontStep hbody (c + 1) rs, ?_⟩
  refine ⟨{ spec.bodyStep ((reentry spec sb c).base) with lpc := 2 + lbody.length }, ?_, ?_, ?_⟩
  · exact loop_lsem_correct fn top spec sb c hterm
  · -- encode (front post-state) = reentry (c+1); its data = bodyStep (reentry c).base
    rw [enc_frontForRun_eq_reentry E sb rs hstart (c + 1), reentry_succ_data]
  · rw [enc_frontForRun_eq_reentry E sb rs hstart (c + 1), reentry_succ_data]

/-! ### Loop CT (robust): the front loop's emitted leak is state-independent

`loopLR_lsemLeak_state_independent` is the loop's constant-time statement: the
back-edge `Lcond` tests only the public counter `"NZ"` (its leak is a constant
`branch`), and the body leaks only syntax — so the whole `loopLR` leak is the same
from any two states. The front `RFor`'s public counter (`cmdCT (.RFor …)` adds no
guard) is exactly the source-level fact this realises. -/

/-- **`front_loop_lsem_robust`.** The front counted loop's emitted leak is
    state-independent (constant-time): the real emitted loop `loopLR` leaks the
    same trace from any two `lsem` states, given the body's leak is
    state-independent (`hbody`) and always completes (`hsucc`). This is
    `loopLR_lsemLeak_state_independent` — the back-edge tests only the public
    static trip count. -/
theorem front_loop_lsem_robust {w : Nat} (top : LLabel) (lbody : List LinstrR)
    (hbody : ∀ (sb₁ sb₂ : Lstate w), lsemLeak lbody sb₁ = lsemLeak lbody sb₂)
    (hsucc : ∀ s : Lstate w, (lsemStraight lbody s).isSome) :
    ∀ s₁ s₂ : Lstate w,
      lsemLeak (loopLR "NZ" top lbody) s₁ = lsemLeak (loopLR "NZ" top lbody) s₂ :=
  fun s₁ s₂ => loopLR_lsemLeak_state_independent top lbody hbody hsucc s₁ s₂

/-! ## 5. The front branch `RIfNz` → the emitted `Lcond` branch under the labeled `lsem`

The front `RIfNz cond ct cf` branches on the public scalar `cond`: nonzero ⇒ `ct`,
zero ⇒ `cf` (`RustExec.ifTrue`/`ifFalse`). The emitted form is the standard
labeled-`Lcond` forward branch:

```
   Lcond cond .Lthen      -- cond ≠ 0 ⇒ jump to the then-label; else fall through
   <else block cf>
   Lgoto Lend             -- skip the then block
 .Lthen:
   <then block ct>
 .Lend:
```

run by **`evalInstrP`/`lsemFuel`** (the real `Lcond` arm: nonzero ⇒
`evalJump` to `findLabel .Lthen + 1` = the then-block start; zero ⇒ fall through to
the else block). The `Lcond` reads the SAME scrutinee register the front `RIfNz`
tests. -/

/-- The emitted labeled-`Lcond` branch instruction list for `RIfNz cond ct cf`:
    the conditional jump to `Lthen` (taken when `cond ≠ 0`), the else block `cf`,
    a `Lgoto` to `Lend` (skipping the then block), the then label, the then block
    `ct`, and the end label. `cond` is the scrutinee register; `fn` is the function
    the `Lgoto`/`Lcond` resolve their labels in. -/
def ifLR (fn : String) (cond : String) (lThen lEnd : LLabel)
    (cf ct : List LinstrR) : List LinstrR :=
  (.Lcond (.reg cond) lThen)
    :: cf ++ [.Lgoto (fn, lEnd), .Llabel .internal lThen] ++ ct ++ [.Llabel .internal lEnd]

/-- The branch program: the singleton-function program whose body is `ifLR`. -/
def ifProg (fn : String) (cond : String) (lThen lEnd : LLabel)
    (cf ct : List LinstrR) : Lprog :=
  singletonProg fn (ifLR fn cond lThen lEnd cf ct)

/-- `findInstr` at the branch entry (pc 0) fetches the `Lcond` scrutinee test. -/
theorem findInstr_ifEntry (fn : String) {w : Nat} (cond : String) (lThen lEnd : LLabel)
    (cf ct : List LinstrR) (d : Lstate w) :
    findInstr (ifProg fn cond lThen lEnd cf ct)
        { base := { d with lpc := 0 }, lfn := fn }
      = some (.Lcond (.reg cond) lThen) := by
  rw [ifProg, findInstr_singleton fn (ifLR fn cond lThen lEnd cf ct) _ rfl]
  simp [ifLR]

/-- A block instruction is **label-free** (not a `Llabel`). The realistic emitted
    branch arm is a straight-line block with no internal label declarations, so the
    branch's `Lthen`/`Lend` labels are the *first* occurrences `findLabel` finds.
    (Straight-line `Lopn` / `Lalign` are label-free; a `Llabel` is not.) -/
def LabelFree (i : LinstrR) : Prop := ∀ k l, i ≠ .Llabel k l

/-- `isLabel` is false on a label-free instruction. -/
theorem isLabel_false (lbl : LLabel) (i : LinstrR) (h : LabelFree i) :
    isLabel lbl i = false := by
  cases i <;> first | rfl | exact absurd rfl (h _ _)

/-- `findLabel` finds nothing in an all-label-free block: no `Llabel` to match. -/
theorem findLabel_none_of_labelFree (lbl : LLabel) (blk : List LinstrR)
    (h : ∀ i ∈ blk, LabelFree i) : findLabel lbl blk = none := by
  unfold findLabel
  induction blk with
  | nil => rfl
  | cons a as ih =>
      rw [List.findIdx?_cons, isLabel_false lbl a (h a (by simp))]
      simpa using ih (fun i hi => h i (by simp [hi]))

/-- The then-label `lThen` sits at index `cf.length + 2` in `ifLR` (after the
    `Lcond`, the label-free else block `cf`, and the `Lgoto`). `findLabel` resolves
    it there, so the taken branch jumps to `cf.length + 3` — the start of the then
    block `ct`. Requires `cf` label-free (so no earlier `Llabel` shadows `lThen`). -/
theorem findLabel_ifThen (fn : String) (cond : String) (lThen lEnd : LLabel)
    (cf ct : List LinstrR) (hcf : ∀ i ∈ cf, LabelFree i) :
    findLabel lThen (ifLR fn cond lThen lEnd cf ct) = some (cf.length + 2) := by
  -- Lean associates `ifLR` as `((Lcond :: cf) ++ [Lgoto, Llabel lThen]) ++ ct) ++ [Llabel lEnd]`.
  -- Regroup as `(Lcond :: cf) ++ (Lgoto :: Llabel lThen :: (ct ++ [Llabel lEnd]))`.
  have hre : ifLR fn cond lThen lEnd cf ct
      = ((.Lcond (.reg cond) lThen) :: cf)
          ++ (LinstrR.Lgoto (fn, lEnd) :: .Llabel .internal lThen
                :: (ct ++ [LinstrR.Llabel .internal lEnd])) := by
    simp [ifLR]
  unfold findLabel
  rw [hre, List.findIdx?_append]
  -- prefix `Lcond :: cf` is label-free ⇒ `none`.
  have hpre : ((.Lcond (.reg cond) lThen) :: cf).findIdx? (isLabel lThen) = none := by
    have := findLabel_none_of_labelFree lThen ((.Lcond (.reg cond) lThen) :: cf)
      (by intro i hi; rcases List.mem_cons.mp hi with h | h
          · subst h; intro k l; simp
          · exact hcf i h)
    simpa [findLabel] using this
  rw [hpre]
  simp only [Option.none_or]
  -- suffix: `Lgoto :: Llabel lThen :: …`; first label match at index 1.
  rw [List.findIdx?_cons, isLabel_false lThen (.Lgoto (fn, lEnd)) (by intro k l; simp)]
  simp only [Bool.false_eq_true, if_false]
  rw [List.findIdx?_cons,
    show isLabel lThen (.Llabel .internal lThen) = true from by simp [isLabel]]
  simp only [if_true, Option.map_some, List.length_cons]
  congr 1
  omega

/-- The `Lfundef` body of the branch program, mapped back through `li_i`, is
    exactly `ifLR` — the list `evalJump`'s `findLabel` resolves against. -/
theorem ifProg_body_li (fn : String) (cond : String) (lThen lEnd : LLabel)
    (cf ct : List LinstrR) :
    ((getFundef (ifProg fn cond lThen lEnd cf ct) fn).map
        (fun fd => fd.lfd_body.map Linstr.li_i))
      = some (ifLR fn cond lThen lEnd cf ct) := by
  rw [ifProg, getFundef_singleton]
  simp only [Option.map_some]
  congr 1
  rw [List.map_map, show (Linstr.li_i ∘ fun ir => (⟨0, ir⟩ : Linstr)) = id from rfl, List.map_id]

/-- **Branch decision — TAKEN** (`cond ≠ 0`): from the branch entry (pc 0), the
    `Lcond` reads the public scrutinee register `cond`; nonzero ⇒ `evalJump` to
    `findLabel lThen + 1 = cf.length + 3` — the start of the THEN block `ct` (after
    the `Lcond`, the else block `cf`, the `Lgoto`, and the `Llabel lThen`). This is
    the `lsem` realisation of `RustExec.ifTrue`. Requires `cf` label-free. -/
theorem ifEntry_taken (fn : String) {w : Nat} (cond : String) (lThen lEnd : LLabel)
    (cf ct : List LinstrR) (d : Lstate w) (fuel : Nat)
    (hcf : ∀ i ∈ cf, LabelFree i) (hne : d.lvm cond ≠ 0) :
    lsemFuel (ifProg fn cond lThen lEnd cf ct) (fuel + 1)
        { base := { d with lpc := 0 }, lfn := fn }
      = lsemFuel (ifProg fn cond lThen lEnd cf ct) fuel
          { base := { d with lpc := cf.length + 3 }, lfn := fn } := by
  rw [lsemFuel, findInstr_ifEntry fn cond lThen lEnd cf ct d]
  simp only [evalInstrP, evalOperand]
  simp only [ne_eq, hne, not_false_eq_true, ↓reduceIte]
  have hbody := ifProg_body_li fn cond lThen lEnd cf ct
  simp only [evalJump, ifProg, getFundef_singleton, Option.map_some,
    Option.some.injEq] at hbody ⊢
  rw [hbody, findLabel_ifThen fn cond lThen lEnd cf ct hcf]
  -- jump target pc = (cf.length + 2) + 1 = cf.length + 3.
  simp only [LstateP.setcpc]

/-- **Branch decision — NOT TAKEN** (`cond = 0`): from the branch entry (pc 0), the
    `Lcond` reads the public scrutinee `cond`; zero ⇒ fall through to pc `1` — the
    start of the ELSE block `cf`. This is the `lsem` realisation of
    `RustExec.ifFalse`. (No label hypothesis needed — fall-through is a pc bump.) -/
theorem ifEntry_fallthrough (fn : String) {w : Nat} (cond : String) (lThen lEnd : LLabel)
    (cf ct : List LinstrR) (d : Lstate w) (fuel : Nat) (hz : d.lvm cond = 0) :
    lsemFuel (ifProg fn cond lThen lEnd cf ct) (fuel + 1)
        { base := { d with lpc := 0 }, lfn := fn }
      = lsemFuel (ifProg fn cond lThen lEnd cf ct) fuel
          { base := { d with lpc := 1 }, lfn := fn } := by
  rw [lsemFuel, findInstr_ifEntry fn cond lThen lEnd cf ct d]
  simp only [evalInstrP, evalOperand]
  simp only [ne_eq, hz, not_true_eq_false, ↓reduceIte]
  -- fall through: `s.nextPc` bumps pc 0 → 1.
  simp only [LstateP.nextPc, Lstate.nextPc]

/-! ### Branch CT: the `Lcond` decision leak is the constant `branch`

The branch's leading control-flow instruction is the `Lcond (.reg cond) lThen`,
whose leak (`linstrLeak`) is the constant `[LLeak.branch]` — it reads the
instruction *syntax*, never `s.lvm`. So the **branch-decision leak is
state-independent**: the conditional jump leaks nothing about the scrutinee value
beyond the (public) fact that a branch occurs. This is the CT content of a
branch and is constant-time **precisely when the scrutinee is public**
(`cmdCT_RIfNz`'s `lt cond = .Public`): the public-vs-secret classification of
`cond` is what makes "a branch happened here" a public, rather than secret,
observation. (Scope: the *arms'* leaks are a separate obligation — each arm
`cf` / `ct` is a straight-line block whose own leak is state-independent by the
straight-line theory `JasminLsemRobust`; the labeled `lsemLeak` does not thread
*through* the `Lcond`/`Lgoto` control transfers, so the arm leaks are not folded in
here.) -/

/-- **Branch-decision constant-time.** The leak `lsemLeak` of the emitted branch
    `ifLR`, observed at the `Lcond` decision, is the constant `[LLeak.branch]` —
    the **same from any two states**. The conditional jump leaks only the syntactic
    fact "a branch", never the scrutinee value. CT requires the scrutinee public
    (`cmdCT_RIfNz`): a secret scrutinee would make this `branch` observation
    secret-dependent in the surrounding program. -/
theorem ifLR_decision_leak {w : Nat} (fn : String) (cond : String)
    (lThen lEnd : LLabel) (cf ct : List LinstrR) (s : Lstate w) :
    lsemLeak (ifLR fn cond lThen lEnd cf ct) s = [LLeak.branch] := by
  -- regroup `ifLR` so the head is the `Lcond`.
  have hre : ifLR fn cond lThen lEnd cf ct
      = (.Lcond (.reg cond) lThen)
          :: (cf ++ (LinstrR.Lgoto (fn, lEnd) :: .Llabel .internal lThen
                :: (ct ++ [LinstrR.Llabel .internal lEnd]))) := by
    simp [ifLR]
  rw [hre, lsemLeak_cons]
  -- the head `Lcond` leaks `[branch]`; its straight-line `lsemStep` is `none`
  -- (control transfer is out of the straight-line stepper), so the tail leak is
  -- `[]` — the trace is exactly the constant decision `[branch]`, from any state.
  simp only [linstrLeak]
  rfl

/-- The branch-decision leak is state-independent (immediate from
    `ifLR_decision_leak`: it is the same constant from any two states). -/
theorem ifLR_lsemLeak_state_independent {w : Nat} (fn : String) (cond : String)
    (lThen lEnd : LLabel) (cf ct : List LinstrR) (s₁ s₂ : Lstate w) :
    lsemLeak (ifLR fn cond lThen lEnd cf ct) s₁
      = lsemLeak (ifLR fn cond lThen lEnd cf ct) s₂ := by
  rw [ifLR_decision_leak, ifLR_decision_leak]

/-! ## 6. Capstone (branch): the front `RIfNz`'s emitted `Lcond` realises the
source decision, and is constant-time for a public scrutinee -/

/-- **`front_if_lsem_correct`.** The **real emitted** labeled-`Lcond` branch
    `ifProg cond` (run by `evalInstrP`/`lsemFuel`) realises the source
    two-branch decision of `RIfNz cond ct cf`, reading the SAME scrutinee register
    `cond` the front `RIfNz` tests:

    * (taken — the `lsem` image of `RustExec.ifTrue`) when the emitted scrutinee
      `d.lvm cond ≠ 0`, the `Lcond` jumps to the THEN block `ct` (pc `cf.length+3`,
      via `evalJump`'s `findLabel lThen + 1`); and
    * (fall-through — the `lsem` image of `RustExec.ifFalse`) when `d.lvm cond = 0`,
      the `Lcond` falls through to the ELSE block `cf` (pc `1`).

    Constant-time when the scrutinee is public (`cmdCT_RIfNz`'s requirement, stated
    by construction): the `Lcond` leaks the constant `branch` regardless of `d.lvm cond`
    (`ifLR_decision_leak`). `cf` is label-free (the realistic straight-line emitted
    arm). No `JasminIRToX86` edge, no `jasminc_preserves_ct`. The explicit tie to
    the front `RustExec` two-branch is `front_if_RustExec_corresponds` below. -/
theorem front_if_lsem_correct (fn : String) {w : Nat} (cond : String)
    (lThen lEnd : LLabel) (cf ct : List LinstrR) (d : Lstate w) (fuel : Nat)
    (hcf : ∀ i ∈ cf, LabelFree i) :
    -- (taken) front scalar nonzero ⇒ emitted `Lcond` enters the THEN block `ct`.
    (d.lvm cond ≠ 0 →
      lsemFuel (ifProg fn cond lThen lEnd cf ct) (fuel + 1)
          { base := { d with lpc := 0 }, lfn := fn }
        = lsemFuel (ifProg fn cond lThen lEnd cf ct) fuel
            { base := { d with lpc := cf.length + 3 }, lfn := fn })
    ∧
    -- (fall-through) front scalar zero ⇒ emitted `Lcond` enters the ELSE block `cf`.
    (d.lvm cond = 0 →
      lsemFuel (ifProg fn cond lThen lEnd cf ct) (fuel + 1)
          { base := { d with lpc := 0 }, lfn := fn }
        = lsemFuel (ifProg fn cond lThen lEnd cf ct) fuel
            { base := { d with lpc := 1 }, lfn := fn }) :=
  ⟨fun hne => ifEntry_taken fn cond lThen lEnd cf ct d fuel hcf hne,
   fun hz => ifEntry_fallthrough fn cond lThen lEnd cf ct d fuel hz⟩

/-- **The front `RustExec` two-branch corresponds to the emitted `Lcond` decision.**
    Given a scrutinee encoding `hscr : (rs.rsScalar cond ≠ 0) ↔ (d.lvm cond ≠ 0)`
    (the emitted register `cond` is nonzero iff the front scalar is — the encoding
    edge), the branch the front `RustExec` of `RIfNz cond ct cf` takes is exactly
    the block the emitted `Lcond` enters:

    * whenever the front semantics fires `RustExec.ifTrue` (front scalar nonzero),
      the emitted `Lcond` enters the THEN block `ct`; and
    * whenever it fires `RustExec.ifFalse` (front scalar zero), the emitted `Lcond`
      enters the ELSE block `cf`.

    This is the explicit `RustExec`-level statement of the front-to-emitted branch
    tie; the underlying `lsem` steps are `front_if_lsem_correct`. -/
theorem front_if_RustExec_corresponds (fn : String) {w : Nat} (cond : String)
    (lThen lEnd : LLabel) (cf ct : List LinstrR) (d : Lstate w) (fuel : Nat)
    (rs : RustState) (hcf : ∀ i ∈ cf, LabelFree i)
    (hscr : (rs.rsScalar cond ≠ 0) ↔ (d.lvm cond ≠ 0)) :
    -- (front ifTrue ⇒ emitted enters THEN)
    (rs.rsScalar cond ≠ 0 →
      lsemFuel (ifProg fn cond lThen lEnd cf ct) (fuel + 1)
          { base := { d with lpc := 0 }, lfn := fn }
        = lsemFuel (ifProg fn cond lThen lEnd cf ct) fuel
            { base := { d with lpc := cf.length + 3 }, lfn := fn })
    ∧
    -- (front ifFalse ⇒ emitted enters ELSE)
    (rs.rsScalar cond = 0 →
      lsemFuel (ifProg fn cond lThen lEnd cf ct) (fuel + 1)
          { base := { d with lpc := 0 }, lfn := fn }
        = lsemFuel (ifProg fn cond lThen lEnd cf ct) fuel
            { base := { d with lpc := 1 }, lfn := fn }) := by
  refine ⟨fun hne => ifEntry_taken fn cond lThen lEnd cf ct d fuel hcf (hscr.mp hne),
          fun hz => ifEntry_fallthrough fn cond lThen lEnd cf ct d fuel ?_⟩
  by_contra hd
  exact (hscr.mpr hd) (by rw [hz])

/-! ## 7. Combined capstone: front control flow — correct AND robust (constant-time)

A single statement packaging the counted-loop tie (§4) and the branch tie (§5–6):
the front `RFor` / `RIfNz` constructs' emitted control flow, run by the real
labeled `lsem`, realises their `RustExec` source meaning AND is constant-time
under the public-control-flow hypotheses (public trip count / public scrutinee),
with no `JasminIRToX86` edge and no `jasminc_preserves_ct`. -/

/-- **`front_control_lsem_correct_and_robust`.** The front control-flow capstone:

    1. *(loop, correct)* the front `RFor x (c+1) body`'s `RustExec` post-state is
       the `(c+1)`-fold front fold, and the real emitted loop `loopProg`'s `lsem`
       run halts at the `lsem` data encoding it (`front_loop_lsem_correct`);
    2. *(loop, robust / CT)* the emitted loop's leak is state-independent over a
       public trip count (`front_loop_lsem_robust`);
    3. *(branch, correct)* the front `RIfNz cond ct cf`'s decision is realised by
       the real emitted `Lcond` branch — THEN on nonzero, ELSE on zero
       (`front_if_lsem_correct`);
    4. *(branch, robust / CT)* the emitted branch's **decision leak** is the
       constant `branch`, state-independent (`ifLR_lsemLeak_state_independent`) —
       constant-time for a public scrutinee (`cmdCT_RIfNz`).

    All four reuse the REAL emitted forms (`loopLR`/`loopProg` = `loopLcmd` modulo
    the dropped `CMP`; the labeled `Lcond` branch run by `evalInstrP`). Public
    control-flow hypotheses (stated, not hidden): `LoopTerminatesIn` (public trip
    count) and label-freedom of the straight-line else arm; the branch-decision CT
    is the public-scrutinee `cmdCT_RIfNz` shape (a secret scrutinee makes the
    `branch` observation secret-dependent). -/
theorem front_control_lsem_correct_and_robust
    {N : Nat} {leafSpec : LeafSpec}
    -- loop data:
    (x : String) (lpBody : LowCT) (frontStep : Nat → RustState → RustState)
    (hbody : ∀ (i : Nat) (rs : RustState),
        RustExec N leafSpec lpBody (rsSetScalar rs x i) (frontStep i rs))
    (fnL : String) {w : Nat} (topL : LLabel) {llBody : List LinstrR}
    (spec : LoopBodySpec w llBody) (sb : Lstate w) (c : Nat)
    (htermL : LoopTerminatesIn spec sb c)
    (E : FrontLoopEncodes spec frontStep) (rs : RustState)
    (hstartL : E.enc rs = { sb with lpc := 1 })
    (hbodyLeak : ∀ (sb₁ sb₂ : Lstate w), lsemLeak llBody sb₁ = lsemLeak llBody sb₂)
    (hbodySucc : ∀ s : Lstate w, (lsemStraight llBody s).isSome)
    -- branch data:
    (fnB : String) (cond : String) (lThen lEnd : LLabel) (cf ct : List LinstrR)
    (d : Lstate w) (fuel : Nat) (hcf : ∀ i ∈ cf, LabelFree i) :
    -- (1) loop correct
    (RustExec N leafSpec (.RFor x (c + 1) lpBody) rs (frontForRun frontStep (c + 1) rs)
      ∧ ∃ t : Lstate w,
          lsemFuel (loopProg fnL topL llBody) ((c + 1) * (llBody.length + 1) + 1)
              { base := { sb with lpc := 0 }, lfn := fnL }
            = some { base := t, lfn := fnL }
        ∧ t.lvm = (E.enc (frontForRun frontStep (c + 1) rs)).lvm
        ∧ t.lmem = (E.enc (frontForRun frontStep (c + 1) rs)).lmem)
    ∧
    -- (2) loop robust / CT
    (∀ s₁ s₂ : Lstate w,
      lsemLeak (loopLR "NZ" topL llBody) s₁ = lsemLeak (loopLR "NZ" topL llBody) s₂)
    ∧
    -- (3) branch correct (taken / fall-through)
    ((d.lvm cond ≠ 0 →
        lsemFuel (ifProg fnB cond lThen lEnd cf ct) (fuel + 1)
            { base := { d with lpc := 0 }, lfn := fnB }
          = lsemFuel (ifProg fnB cond lThen lEnd cf ct) fuel
              { base := { d with lpc := cf.length + 3 }, lfn := fnB })
      ∧ (d.lvm cond = 0 →
        lsemFuel (ifProg fnB cond lThen lEnd cf ct) (fuel + 1)
            { base := { d with lpc := 0 }, lfn := fnB }
          = lsemFuel (ifProg fnB cond lThen lEnd cf ct) fuel
              { base := { d with lpc := 1 }, lfn := fnB }))
    ∧
    -- (4) branch robust / CT
    (∀ s₁ s₂ : Lstate w,
      lsemLeak (ifLR fnB cond lThen lEnd cf ct) s₁
        = lsemLeak (ifLR fnB cond lThen lEnd cf ct) s₂) :=
  ⟨front_loop_lsem_correct x lpBody frontStep hbody fnL topL spec sb c htermL E rs hstartL,
   front_loop_lsem_robust topL llBody hbodyLeak hbodySucc,
   front_if_lsem_correct fnB cond lThen lEnd cf ct d fuel hcf,
   fun s₁ s₂ =>
     ifLR_lsemLeak_state_independent fnB cond lThen lEnd cf ct s₁ s₂⟩

end CatCrypt.Crypto.SecureCompilation.VIR.FrontControlLsem
