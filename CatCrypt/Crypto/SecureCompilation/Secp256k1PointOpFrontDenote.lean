/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontCovered
public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontCovered
public meta import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpCompositional
public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpCompositional

/-!
# The front-compiled secp256k1 `jacDbl` kernel, from `Com.denote` to the schedule

Two steps join `Secp256k1PointOpCompositional`'s schedule-level value tie to the
denotation of the front-compiled point-op `Com`.

**Step 1 — the `Com` denotation is the source waist.**
`Secp256k1PointOpFrontCovered.jacDblBody_coveredSCtl` places the `jacDbl` front
body in the covered scalar fragment, so
`TranslateDialectScalar.translateDialectControl_denote_ctl` applies to it:
the descended `Com catCryptDialect` denotes exactly the 12-cell output frame the
source semantics `semScalar` leaves in the tracked name `out`
(`jacDblFront_denote`).

The `Com` in that statement is the front's own `ret out` cap: `o` is the output
of `translateDialectControl inVM2 jacDblBody` and `com` is `o.cont` applied to
`Com.ret` at the slot `o.vm` resolves `out` to — the two matches
`Secp256k1PointOpFront.jacDblFrontCom` is defined by. Rewriting that definition
inside a proof forces the match scrutinee
`translateDialectControl inVM2 jacDblBody`, the measured out-of-memory
evaluation of a single whole-op `Com.denote` (over 11 GB), so the two matches
appear as the hypotheses `hTrans` and `hName` instead.

**Step 2 — the source waist decomposes along the brick boundaries.**
`semScalar_seqAll_append` splits the waist semantics of a `seqAll` at any
concatenation point, and `brickFold_scheduleEval` folds the resulting per-brick
chain into `Secp256k1PointOpCompositional.scheduleEvalG` on the half-limb
residue readout `feVal`. Composing with
`Secp256k1PointOpCompositional.jacDblSchedule_realizes_spec` gives
`jacDblSchedule_waist_value`: the waist semantics of the whole 19-brick schedule
carries the `dbl-2009-l` formulas over `ℤ/pℤ`. No `Com` is evaluated anywhere.

## The remaining obligation

Step 2 is stated over `BrickStep`, the per-brick field obligation: that one
emitted brick's waist semantics writes `fm`/`fa`/`fs` of its operands' half-limb
readout into the output field element, and leaves every other schedule-visible
field element's readout alone. `BrickStep` states that with no entry condition
and is refutable — its docstring below carries the counterexample. The usable
form is `Secp256k1PointOpBrickInv.BrickStepInv`, parametric in an entry
predicate each brick assumes and re-establishes, and
`Secp256k1PointOpBrickScope.brickStepInv_brickScope` discharges it at
`Secp256k1FeAddSubBrick.BrickScope`. So the schedule waist carries the
`dbl-2009-l` and `add-2007-bl` formulas with no residual hypothesis
(`jacDblSchedule_waist_value_brickScope`, `jacAddSchedule_waist_value_brickScope`),
proved symbolically rather than on the 4-limb KAT battery that
`Secp256k1PointOpFront.secp256k1FeAddFront_denote` and its siblings check.

Two gaps separate that waist value from a value statement about the 12-cell
memref frame: the prologue `loadField` (frame cells to half-limbs) and the
epilogue `storeField` (half-limbs back to frame cells).

## Main results

* `jacDblFront_denote` — the descended point-op `Com` denotes the `semScalar`
  output frame.
* `semScalar_seqAll_append`, `semScalar_seqAll_flatten` — the waist semantics of
  a `seqAll` splits at a concatenation.
* `feVal`, `BrickStep` — the half-limb residue readout and the per-brick field
  obligation over it.
* `brickFold_scheduleEval` — under `BrickStep`, a chain of bricks realizes
  `scheduleEvalG` on the readout.
* `jacDblSchedule_waist_value` — under `BrickStep`, the `jacDbl` schedule's waist
  semantics carries `jacDblSpec`.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontDenote

open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront (seqAll)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontCovered
  (jacDblBody_coveredSCtl jacAddBody_coveredSCtl)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpCompositional
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl

/-! ## 1. The `Com` denotation of the front-compiled kernel -/

/-- **The front-compiled `jacDbl` kernel denotes the source waist's output frame.**

`o` is what the direct control front makes of `jacDblBody` over the point-op
argument context `[P, out]`, `w` is the slot its post-varmap resolves `out` to,
and `com` is the emitted prefix capped with `ret out` — the kernel
`Secp256k1PointOpFront.jacDblFrontCom` names. If the entry valuation `V` is
consistent with the entry environment `env` and the source semantics runs the
body to `env'`, then `com.denote V` is the 12-cell frame `env'` holds at `out`.

Instance of `translateDialectControl_denote_ctl` at `jacDblBody`, with the
coverage discharged by `jacDblBody_coveredSCtl` and the return slot read by
`ConsistentS.lookup_eq`. -/
theorem jacDblFront_denote
    (o : DTransOut inΓ2) (V : Ctxt.Valuation (d := catCryptDialect) inΓ2)
    (env env' : SEnvScalar) (w : CVar o.Γ' (.memref 12))
    (arr : ⟦(CryptoTy.memref 12)⟧) (com : Com catCryptDialect inΓ2 (.memref 12))
    (hTrans : translateDialectControl inVM2 jacDblBody = some o)
    (hCons : ConsistentS inVM2 V env)
    (hSem : semScalar jacDblBody env = some env')
    (hName : o.vm.lookup "out" = some ⟨.memref 12, w⟩)
    (hVal : env' "out" = some ⟨.memref 12, arr⟩)
    (hRet : o.cont (Com.ret (toVIRVar w)) = some com) :
    com.denote V = arr := by
  obtain ⟨V', hc', hcont⟩ :=
    translateDialectControl_denote_ctl jacDblBody_coveredSCtl inVM2 V env env' o
      hCons hTrans hSem
  obtain ⟨com', hcom', hden⟩ := hcont (Com.ret (toVIRVar w))
  rw [hRet] at hcom'
  obtain rfl := Option.some.inj hcom'
  rw [hden]
  exact hc'.lookup_eq hName hVal

/-- **The front-compiled `jacAdd` kernel denotes the source waist's output
    frame.** The `jacDblFront_denote` statement over the binary point-op argument
    context `[P2, P1, out]`: `o` is what the direct control front makes of
    `jacAddBody`, `w` the slot its post-varmap resolves `out` to, and `com` the
    emitted prefix capped with `ret out` — the kernel
    `Secp256k1PointOpFront.jacAddFrontCom` names. -/
theorem jacAddFront_denote
    (o : DTransOut inΓ3) (V : Ctxt.Valuation (d := catCryptDialect) inΓ3)
    (env env' : SEnvScalar) (w : CVar o.Γ' (.memref 12))
    (arr : ⟦(CryptoTy.memref 12)⟧) (com : Com catCryptDialect inΓ3 (.memref 12))
    (hTrans : translateDialectControl inVM3 jacAddBody = some o)
    (hCons : ConsistentS inVM3 V env)
    (hSem : semScalar jacAddBody env = some env')
    (hName : o.vm.lookup "out" = some ⟨.memref 12, w⟩)
    (hVal : env' "out" = some ⟨.memref 12, arr⟩)
    (hRet : o.cont (Com.ret (toVIRVar w)) = some com) :
    com.denote V = arr := by
  obtain ⟨V', hc', hcont⟩ :=
    translateDialectControl_denote_ctl jacAddBody_coveredSCtl inVM3 V env env' o
      hCons hTrans hSem
  obtain ⟨com', hcom', hden⟩ := hcont (Com.ret (toVIRVar w))
  rw [hRet] at hcom'
  obtain rfl := Option.some.inj hcom'
  rw [hden]
  exact hc'.lookup_eq hName hVal

/-! ## 2. The waist semantics splits along a command-list concatenation

`seqAll` chains a flat command list into an `RSeq` spine, so its waist semantics
is a left-to-right `Option`-bind of the per-block semantics. These are the
lemmas that let the point op be reasoned about one brick at a time. -/

/-- The waist semantics of a `seqAll` peels its head command. -/
theorem semScalar_seqAll_cons (c : LowCT) (l : List LowCT) (env : SEnvScalar) :
    semScalar (seqAll (c :: l)) env
      = (semScalar c env).bind (fun e => semScalar (seqAll l) e) := by
  cases l with
  | nil =>
      show semScalar c env = (semScalar c env).bind (fun e => some e)
      cases semScalar c env <;> rfl
  | cons c' cs => rfl

/-- **The waist semantics of a `seqAll` splits at a concatenation.** -/
theorem semScalar_seqAll_append : ∀ (l₁ l₂ : List LowCT) (env : SEnvScalar),
    semScalar (seqAll (l₁ ++ l₂)) env
      = (semScalar (seqAll l₁) env).bind (fun e => semScalar (seqAll l₂) e) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ env; rfl
  | cons c cs ih =>
      intro l₂ env
      rw [List.cons_append, semScalar_seqAll_cons, semScalar_seqAll_cons]
      cases semScalar c env with
      | none => rfl
      | some e => simpa using ih l₂ e

/-- The per-block bind chain over a list of blocks is the waist semantics of
    their flattening. -/
theorem foldl_semScalar_seqAll : ∀ (ls : List (List LowCT)) (o : Option SEnvScalar),
    ls.foldl (fun oe l => oe.bind (fun e => semScalar (seqAll l) e)) o
      = o.bind (fun e => semScalar (seqAll ls.flatten) e) := by
  intro ls
  induction ls with
  | nil => intro o; cases o <;> rfl
  | cons l ls ih =>
      intro o
      rw [List.foldl_cons, ih, List.flatten_cons]
      cases o with
      | none => rfl
      | some e => simpa using (semScalar_seqAll_append l ls.flatten e).symm

/-- **The waist semantics of a flattened block list is the per-block bind fold.** -/
theorem semScalar_seqAll_flatten (ls : List (List LowCT)) (env : SEnvScalar) :
    semScalar (seqAll ls.flatten) env
      = ls.foldl (fun oe l => oe.bind (fun e => semScalar (seqAll l) e)) (some env) := by
  rw [foldl_semScalar_seqAll]
  rfl

/-! ## 3. The half-limb residue readout and the per-brick obligation -/

/-- The residue a field element's eight 32-bit half-limb slots carry:
    `Σ_{k<8} 2^{32k} · env⟦fe h k⟧`. -/
def feVal (env : SEnvScalar) (fe : String) : Nat :=
  ((List.range 8).map (fun k => 2 ^ (32 * k) * (envReader env s!"{fe}h{k}").toNat)).sum

/-- A field-element name the schedule addresses. The schedule's names begin with
    an upper-case letter, while every slot a brick writes privately is under its
    `op{i}` prefix, so the test separates the two. -/
def schedNameB (s : String) : Bool := match s.toList with | c :: _ => c.isUpper | [] => false

/-- All three field-element names of a schedule entry are schedule names. -/
def FOpSchedOkB : FOp → Bool
  | .mul o a b => schedNameB o && schedNameB a && schedNameB b
  | .add o a b => schedNameB o && schedNameB a && schedNameB b
  | .sub o a b => schedNameB o && schedNameB a && schedNameB b

/-- **The per-brick field obligation.** One emitted brick's waist semantics moves
    the half-limb residue readout by exactly one `stepFOpG` at the base-field ops
    `fm`/`fa`/`fs`: the output field element ends holding the field operation
    applied to the operands' readout, and every other schedule-name field
    element's readout is unchanged.

    The 4-limb `native_decide` gates
    `Secp256k1PointOpFront.secp256k1FeAddFront_denote` /
    `secp256k1FeSubFront_denote` and the phase-1 `feMul` gate check this on a KAT
    battery for the standalone single-op fronts.

    **This proposition is FALSE as stated, so every result below conditioned on
    it holds vacuously.** It quantifies over all `env` with no entry condition,
    while the bricks are correct only when each half-limb is `< 2^32` — the
    carry-free discipline `Secp256k1FeMulFront`'s header states
    (`(2^32-1) + (2^32-1)^2 + (2^32-1) = 2^64 - 1`). `feVal` is a plain
    `Σ 2^(32k) · toNat` and does not enforce it. Counterexample at
    `op = .mul o a b`: bind `{a}h0` and `{b}h0` to `2^32` and every other
    half-limb to `0`, with `ZZ ↦ 0`, `CC0 ↦ 977`, `CC1 ↦ 1`, `PL0..PL7 ↦ pl32`.
    Every read is bound, so the brick runs; but `SExpr.evalBV`'s `SMul` is
    `BitVec 64` multiplication, so `2^32 · 2^32` wraps to `0`, every partial
    product is `0`, the folds carry `0`, the final select yields `0`, and
    `feVal env' o = 0` where `stepFOpG` demands `2^64`.

    The repair is not local: `brickFold_scheduleEval` chains bricks, so the
    obligation must be invariant-PRESERVING — each brick assuming the entry
    conditions and re-establishing them for the next. `Secp256k1FeMulBrickFrame`
    carries that shape for the multiply arm (`MulEntry`, `MulBrickValue`,
    `brickStepMul_of_value`), together with the frame half, which is
    unconditionally true. -/
def BrickStep : Prop :=
  ∀ (i : Nat) (op : FOp) (env env' : SEnvScalar),
    semScalar (seqAll (emitFOp i op)) env = some env' →
    ∀ fe : String, schedNameB fe = true →
      feVal env' fe = stepFOpG fm fa fs (feVal env) op fe

/-! ## 4. From the per-brick obligation to the schedule interpreter -/

/-- One schedule step reads only its two operand names and writes only its output
    name, so it respects agreement on schedule names. -/
theorem stepFOpG_congr (FM FA FS : Nat → Nat → Nat) (op : FOp)
    (hop : FOpSchedOkB op = true) (e1 e2 : String → Nat)
    (h : ∀ s, schedNameB s = true → e1 s = e2 s) :
    ∀ s, schedNameB s = true → stepFOpG FM FA FS e1 op s = stepFOpG FM FA FS e2 op s := by
  intro s hs
  cases op with
  | mul o a b =>
      simp only [FOpSchedOkB, Bool.and_eq_true] at hop
      simp only [stepFOpG, envUpd, h a hop.1.2, h b hop.2]
      by_cases hso : s = o
      · simp [hso]
      · simp [hso, h s hs]
  | add o a b =>
      simp only [FOpSchedOkB, Bool.and_eq_true] at hop
      simp only [stepFOpG, envUpd, h a hop.1.2, h b hop.2]
      by_cases hso : s = o
      · simp [hso]
      · simp [hso, h s hs]
  | sub o a b =>
      simp only [FOpSchedOkB, Bool.and_eq_true] at hop
      simp only [stepFOpG, envUpd, h a hop.1.2, h b hop.2]
      by_cases hso : s = o
      · simp [hso]
      · simp [hso, h s hs]

/-- The schedule interpreter respects agreement on schedule names. -/
theorem scheduleEvalG_congr (FM FA FS : Nat → Nat → Nat) :
    ∀ (ops : List FOp) (e1 e2 : String → Nat),
      (∀ op ∈ ops, FOpSchedOkB op = true) →
      (∀ s, schedNameB s = true → e1 s = e2 s) →
      ∀ s, schedNameB s = true →
        scheduleEvalG FM FA FS ops e1 s = scheduleEvalG FM FA FS ops e2 s := by
  intro ops
  induction ops with
  | nil => intro e1 e2 _ h s hs; exact h s hs
  | cons op ops ih =>
      intro e1 e2 hops h s hs
      exact ih _ _ (fun o ho => hops o (.tail _ ho))
        (stepFOpG_congr FM FA FS op (hops op (.head _)) e1 e2 h) s hs

/-- **A chain of bricks realizes the schedule interpreter on the half-limb
    readout.** Under the per-brick obligation, running a list of emitted bricks
    through the waist semantics moves the readout by `scheduleEvalG` at
    `fm`/`fa`/`fs`, on every schedule name. Uses only
    `semScalar_seqAll_append` — no `Com` and no flattened command list is
    evaluated. -/
theorem brickFold_scheduleEval (hB : BrickStep) :
    ∀ (ops : List FOp) (ls : List (List LowCT)),
      List.Forall₂ (fun op l => ∃ i, l = emitFOp i op) ops ls →
      (∀ op ∈ ops, FOpSchedOkB op = true) →
      ∀ (env env' : SEnvScalar),
        semScalar (seqAll ls.flatten) env = some env' →
        ∀ fe, schedNameB fe = true →
          feVal env' fe = scheduleEvalG fm fa fs ops (feVal env) fe := by
  intro ops
  induction ops with
  | nil =>
      intro ls hf _ env env' hsem fe hfe
      cases hf
      simp only [List.flatten_nil] at hsem
      obtain rfl : env' = env := (Option.some.inj hsem).symm
      rfl
  | cons op ops ih =>
      intro ls hf hops env env' hsem fe hfe
      cases hf with
      | cons hl hrest =>
          rename_i l ls'
          obtain ⟨i, rfl⟩ := hl
          rw [List.flatten_cons, semScalar_seqAll_append] at hsem
          cases he : semScalar (seqAll (emitFOp i op)) env with
          | none => rw [he] at hsem; simp at hsem
          | some e1 =>
              rw [he] at hsem
              simp only [Option.bind_some] at hsem
              have hstep := hB i op env e1 he
              have hIH := ih ls' hrest (fun o ho => hops o (.tail _ ho)) e1 env' hsem fe hfe
              rw [hIH]
              exact scheduleEvalG_congr fm fa fs ops (feVal e1)
                (stepFOpG fm fa fs (feVal env) op)
                (fun o ho => hops o (.tail _ ho)) hstep fe hfe

/-- `runSchedule`'s indexed blocks are emitted bricks of their schedule entries. -/
theorem forall2_mapIdx : ∀ (ops : List FOp) (g : Nat → FOp → List LowCT),
    (∀ i op, ∃ j, g i op = emitFOp j op) →
    List.Forall₂ (fun op l => ∃ i, l = emitFOp i op) ops (ops.mapIdx g) := by
  intro ops
  induction ops with
  | nil => intro g _; exact .nil
  | cons a l ih =>
      intro g hg
      rw [List.mapIdx_cons]
      exact .cons (hg 0 a) (ih (fun i => g (i + 1)) (fun i op => hg (i + 1) op))

/-! ## 5. The `dbl-2009-l` schedule at the waist -/

/-- **Under the per-brick obligation, the `jacDbl` schedule's waist semantics
    carries `jacDblSpec`.** From an entry environment whose half-limb readout is
    the input point on the schedule names, running the 19 emitted bricks through
    `semScalar` leaves `Xp`/`Yp`/`Zp` holding the `dbl-2009-l` formulas over
    `ℤ/pℤ`. Composes `brickFold_scheduleEval` with
    `Secp256k1PointOpCompositional.jacDblSchedule_realizes_spec`. -/
theorem jacDblSchedule_waist_value (hB : BrickStep)
    (env env' : SEnvScalar) (X Y Z : Nat)
    (h0 : ∀ fe, schedNameB fe = true → feVal env fe = dblEnv0 X Y Z fe)
    (hSem : semScalar (seqAll (runSchedule jacDblSchedule)) env = some env') :
    (feVal env' "Xp", feVal env' "Yp", feVal env' "Zp") = jacDblSpec X Y Z := by
  have hok : ∀ op ∈ jacDblSchedule, FOpSchedOkB op = true := by decide
  have hfa := forall2_mapIdx jacDblSchedule (fun i op => emitFOp i op) (fun i op => ⟨i, rfl⟩)
  have key := brickFold_scheduleEval hB jacDblSchedule _ hfa hok env env' hSem
  have hcong : ∀ fe, schedNameB fe = true →
      scheduleEvalG fm fa fs jacDblSchedule (feVal env) fe
        = scheduleEval jacDblSchedule (dblEnv0 X Y Z) fe :=
    scheduleEvalG_congr fm fa fs jacDblSchedule (feVal env) (dblEnv0 X Y Z) hok h0
  have hXp : schedNameB "Xp" = true := by decide
  have hYp : schedNameB "Yp" = true := by decide
  have hZp : schedNameB "Zp" = true := by decide
  rw [key "Xp" hXp, key "Yp" hYp, key "Zp" hZp,
    hcong "Xp" hXp, hcong "Yp" hYp, hcong "Zp" hZp]
  exact jacDblSchedule_realizes_spec X Y Z

end CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontDenote
