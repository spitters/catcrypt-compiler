/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresBridgeArith
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT

/-!
# Arithmetic-fragment residuals of the ascent middle tie (`semScalar` ↔ `runBlock`)

`CorresBridgeArith.arith_middle_tie_at_dst` ties the scalar `semScalar` machine
to the flag-carrying `runBlock` machine for a single `ArithSrc` at its **output**
slot `p.dst`.  This module completes the arithmetic residuals:

* **`semLowerSExpr_preserves_nonTmp`** — the `SExpr`-lowering env-mirror
  `semLowerSExpr` binds ONLY fresh `__sx` temporaries, so it leaves every
  non-temp name unchanged.  The frame fact that makes the temporary chain
  invisible to the source-name readout.
* **`arith_middle_tie_nonTmp`** — the middle tie upgraded from the single output
  slot to ALL non-temp names: `semScalar (ArithSrc.toLowCT p) (regEnv st)` agrees
  with `regEnv (runBlock st (lowerArith id p))` on every non-temp name.
* **`arith_middle_tie_seq_nonTmp`** — the block-level tie: for a straight-line
  block `ps : List ArithSrc` (source-clean, well-formed), the folded scalar
  machine `semScalar (ArithSrc.seqToLowCT ps) (regEnv st)` agrees with
  `regEnv (runBlock st (lowerSeq id ps))` on every non-temp name.  Proved through
  a generalized single-step tie (`arith_step_tie_gen`) over any input env
  agreeing with `regEnv st` on non-temp names, threaded by induction on `ps`.

The block tie needs each statement's source reads `a`, `b` to be non-temp
(`isTmpName`-free) so the fresh SExpr temporaries never collide with a source
slot; real arithmetic blocks (named slots, small shift constants) satisfy it.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT

/-! ## Fresh-temp frame helpers -/

/-- Updating an `SEnvScalar` at a fresh temporary `tmpName cnt` leaves every
    non-temp name unchanged (`v ≠ tmpName cnt`, so the guard is `false`). -/
theorem upd_tmpName_nonTmp (env : SEnvScalar) (cnt : Nat) (val : BitVec 64)
    (v : String) (hv : ¬ isTmpName v) :
    (env.upd (tmpName cnt) (t := .sword 64) val) v = env v := by
  have hne : v ≠ tmpName cnt := fun heq => hv ⟨cnt, heq⟩
  simp only [SEnvScalar.upd, if_neg hne]

/-- A single `binNode` step binds a fresh temporary `tmpName cnt`, so it leaves
    every non-temp name unchanged. -/
theorem binNode_preserves_nonTmp (envAB : SEnvScalar) (na nb : String) (cnt : Nat)
    (f : BitVec 64 → BitVec 64 → BitVec 64) (env2 : SEnvScalar) (nm : String) (cnt' : Nat)
    (h : binNode envAB na nb cnt f = some (env2, nm, cnt')) :
    ∀ v, ¬ isTmpName v → env2 v = envAB v := by
  intro v hv
  simp only [binNode] at h
  cases hxa : envReadU64 envAB na with
  | none => simp [hxa] at h
  | some va =>
      cases hxb : envReadU64 envAB nb with
      | none => simp [hxa, hxb] at h
      | some vb =>
          simp only [hxa, hxb, Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.1]
          exact upd_tmpName_nonTmp envAB cnt (f va vb) v hv

/-! ## Deliverable 1 — `semLowerSExpr` preserves every non-temp name -/

/-- **`semLowerSExpr` frame lemma.** The `SExpr`-lowering env-mirror binds only
    fresh `__sx` temporaries, so it leaves the value at every non-temp name
    exactly as it found it.  Structural induction on the `SExpr`: the `SVar` arm
    is a pass-through, the `SLit` arm binds a single fresh temp, and each binary
    arm composes two recursive frames with a `binNode` (all three fresh-temp
    binds land off the non-temp names by `tmpName`'s `__sx` namespace).  The arms
    `semLowerSExpr` declines (`SLt`/`SAsr`/`SMulS`/`SMulHiS`/`SLimb`) are
    vacuous. -/
theorem semLowerSExpr_preserves_nonTmp (env : SEnvScalar) (cnt : Nat) (e : SExpr)
    (env2 : SEnvScalar) (nm : String) (cnt' : Nat)
    (h : semLowerSExpr env cnt e = some (env2, nm, cnt')) :
    ∀ v, ¬ isTmpName v → env2 v = env v := by
  induction e generalizing env cnt env2 nm cnt' with
  | SVar x =>
      intro v hv
      simp only [semLowerSExpr] at h
      cases hx : envReadU64 env x with
      | none => simp [hx] at h
      | some w =>
          simp only [hx, Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.1]
  | SLit n =>
      intro v hv
      simp only [semLowerSExpr, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      exact upd_tmpName_nonTmp env cnt (BitVec.ofNat 64 n) v hv
  | SAdd a b iha ihb =>
      intro v hv
      simp only [semLowerSExpr] at h
      cases hA : semLowerSExpr env cnt a with
      | none => simp [hA] at h
      | some r1 =>
          obtain ⟨e1, na, c1⟩ := r1
          cases hB : semLowerSExpr e1 c1 b with
          | none => simp [hA, hB] at h
          | some r2 =>
              obtain ⟨e2, nb, c2⟩ := r2
              simp only [hA, hB] at h
              rw [binNode_preserves_nonTmp e2 na nb c2 _ env2 nm cnt' h v hv,
                ihb e1 c1 e2 nb c2 hB v hv, iha env cnt e1 na c1 hA v hv]
  | SSub a b iha ihb =>
      intro v hv
      simp only [semLowerSExpr] at h
      cases hA : semLowerSExpr env cnt a with
      | none => simp [hA] at h
      | some r1 =>
          obtain ⟨e1, na, c1⟩ := r1
          cases hB : semLowerSExpr e1 c1 b with
          | none => simp [hA, hB] at h
          | some r2 =>
              obtain ⟨e2, nb, c2⟩ := r2
              simp only [hA, hB] at h
              rw [binNode_preserves_nonTmp e2 na nb c2 _ env2 nm cnt' h v hv,
                ihb e1 c1 e2 nb c2 hB v hv, iha env cnt e1 na c1 hA v hv]
  | SMul a b iha ihb =>
      intro v hv
      simp only [semLowerSExpr] at h
      cases hA : semLowerSExpr env cnt a with
      | none => simp [hA] at h
      | some r1 =>
          obtain ⟨e1, na, c1⟩ := r1
          cases hB : semLowerSExpr e1 c1 b with
          | none => simp [hA, hB] at h
          | some r2 =>
              obtain ⟨e2, nb, c2⟩ := r2
              simp only [hA, hB] at h
              rw [binNode_preserves_nonTmp e2 na nb c2 _ env2 nm cnt' h v hv,
                ihb e1 c1 e2 nb c2 hB v hv, iha env cnt e1 na c1 hA v hv]
  | SShr a b iha ihb =>
      intro v hv
      simp only [semLowerSExpr] at h
      cases hA : semLowerSExpr env cnt a with
      | none => simp [hA] at h
      | some r1 =>
          obtain ⟨e1, na, c1⟩ := r1
          cases hB : semLowerSExpr e1 c1 b with
          | none => simp [hA, hB] at h
          | some r2 =>
              obtain ⟨e2, nb, c2⟩ := r2
              simp only [hA, hB] at h
              rw [binNode_preserves_nonTmp e2 na nb c2 _ env2 nm cnt' h v hv,
                ihb e1 c1 e2 nb c2 hB v hv, iha env cnt e1 na c1 hA v hv]
  | SShl a b iha ihb =>
      intro v hv
      simp only [semLowerSExpr] at h
      cases hA : semLowerSExpr env cnt a with
      | none => simp [hA] at h
      | some r1 =>
          obtain ⟨e1, na, c1⟩ := r1
          cases hB : semLowerSExpr e1 c1 b with
          | none => simp [hA, hB] at h
          | some r2 =>
              obtain ⟨e2, nb, c2⟩ := r2
              simp only [hA, hB] at h
              rw [binNode_preserves_nonTmp e2 na nb c2 _ env2 nm cnt' h v hv,
                ihb e1 c1 e2 nb c2 hB v hv, iha env cnt e1 na c1 hA v hv]
  | SAnd a b iha ihb =>
      intro v hv
      simp only [semLowerSExpr] at h
      cases hA : semLowerSExpr env cnt a with
      | none => simp [hA] at h
      | some r1 =>
          obtain ⟨e1, na, c1⟩ := r1
          cases hB : semLowerSExpr e1 c1 b with
          | none => simp [hA, hB] at h
          | some r2 =>
              obtain ⟨e2, nb, c2⟩ := r2
              simp only [hA, hB] at h
              rw [binNode_preserves_nonTmp e2 na nb c2 _ env2 nm cnt' h v hv,
                ihb e1 c1 e2 nb c2 hB v hv, iha env cnt e1 na c1 hA v hv]
  | SXor a b iha ihb =>
      intro v hv
      simp only [semLowerSExpr] at h
      cases hA : semLowerSExpr env cnt a with
      | none => simp [hA] at h
      | some r1 =>
          obtain ⟨e1, na, c1⟩ := r1
          cases hB : semLowerSExpr e1 c1 b with
          | none => simp [hA, hB] at h
          | some r2 =>
              obtain ⟨e2, nb, c2⟩ := r2
              simp only [hA, hB] at h
              rw [binNode_preserves_nonTmp e2 na nb c2 _ env2 nm cnt' h v hv,
                ihb e1 c1 e2 nb c2 hB v hv, iha env cnt e1 na c1 hA v hv]
  | SLt a b iha ihb => intro v hv; simp [semLowerSExpr] at h
  | SAsr a b iha ihb => intro v hv; simp [semLowerSExpr] at h
  | SMulS a b iha ihb => intro v hv; simp [semLowerSExpr] at h
  | SMulHiU a b iha ihb =>
      intro v hv
      simp only [semLowerSExpr] at h
      cases hA : semLowerSExpr env cnt a with
      | none => simp [hA] at h
      | some r1 =>
          obtain ⟨e1, na, c1⟩ := r1
          cases hB : semLowerSExpr e1 c1 b with
          | none => simp [hA, hB] at h
          | some r2 =>
              obtain ⟨e2, nb, c2⟩ := r2
              simp only [hA, hB] at h
              rw [binNode_preserves_nonTmp e2 na nb c2 _ env2 nm cnt' h v hv,
                ihb e1 c1 e2 nb c2 hB v hv, iha env cnt e1 na c1 hA v hv]
  | SMulHiS a b iha ihb => intro v hv; simp [semLowerSExpr] at h
  | SLimb s k => intro v hv; simp [semLowerSExpr] at h

/-! ## Deliverable 2 — the whole non-temp middle tie for a single `ArithSrc` -/

/-- The machine op-block writes only its destination register `dst`, leaving
    every other register unchanged (`v ≠ p.dst`).  The `runBlock` sibling of
    `runBlock_lowerArith_id_dst`. -/
theorem runBlock_lowerArith_id_other (p : ArithSrc) (st : JState 64) (v : String)
    (hv : v ≠ p.dst) :
    (runBlock st (lowerArith id p)).regs v = st.regs v := by
  cases p with
  | mk dst a op b =>
    have hrun : runBlock st (lowerArith id ⟨dst, a, op, b⟩)
        = evalInstr (st.setReg dst (st.get a)) (op.toJInstr dst (.reg b)) := by
      simp only [lowerArith, id_eq, runBlock_cons, runBlock_nil, evalInstr, x86_MOV,
        JOperand.eval]
    have hget : (runBlock st (lowerArith id ⟨dst, a, op, b⟩)).get v = st.get v := by
      rw [hrun, ArithOp.toJInstr_get_other op dst b _ v hv,
        JState.get_setReg_other st dst v (st.get a) hv]
    simpa [JState.get] using hget

/-- **The non-temp middle tie for `ArithSrc`.**  `semScalar` succeeds on the
    real `LowCT` node `ArithSrc.toLowCT p` over the register view `regEnv st`,
    and its result agrees with the machine register view of the lowered block
    `regEnv (runBlock st (lowerArith id p))` on EVERY non-temp name — the
    `SExpr`-lowering fresh temporaries (which have no machine counterpart) are
    the only slots where the two environments can disagree.  Upgrades
    `arith_middle_tie_at_dst`'s single-slot tie to the whole non-temp fibre. -/
theorem arith_middle_tie_nonTmp (p : ArithSrc) (st : JState 64) (hb : p.b ≠ p.dst) :
    ∃ env', semScalar (ArithSrc.toLowCT p) (regEnv st) = some env'
      ∧ ∀ v, ¬ isTmpName v →
          env' v = regEnv (runBlock st (lowerArith id p)) v := by
  obtain ⟨env', hsem, hdst⟩ := arith_middle_tie_at_dst p st hb
  refine ⟨env', hsem, ?_⟩
  intro v hv
  by_cases hvd : v = p.dst
  · subst hvd
    rw [hdst]
    simp only [regEnv]
  · have hsem2 := hsem
    simp only [ArithSrc.toLowCT, semScalar] at hsem2
    cases hlow : semLowerSExpr (regEnv st) 0 p.toSExpr with
    | none => simp [hlow] at hsem2
    | some r =>
        obtain ⟨env2, nm, cnt'⟩ := r
        simp only [hlow, Option.some.injEq] at hsem2
        rw [← hsem2]
        have hv2 := semLowerSExpr_preserves_nonTmp (regEnv st) 0 p.toSExpr env2 nm cnt' hlow v hv
        simp only [SEnvScalar.upd, if_neg hvd, hv2, regEnv,
          runBlock_lowerArith_id_other p st v hvd]

/-! ## Deliverable 3 — the block-level non-temp tie (`lowerSeq`) -/

/-- On an input env agreeing with `regEnv st` on non-temp names, the scalar
    output value at `dst` equals the machine register `runBlock` leaves in `dst`.
    The `SExpr` word evaluator reads its two source slots `a`, `b` (non-temp)
    through `regEnv`, so it computes exactly the `BitVec 64` op the machine
    block does. -/
theorem evalBV_toSExpr_eq_machine (p : ArithSrc) (st : JState 64) (env : SEnvScalar)
    (ha : ¬ isTmpName p.a) (hbt : ¬ isTmpName p.b) (hb : p.b ≠ p.dst)
    (hagree : ∀ v, ¬ isTmpName v → env v = some ⟨.sword 64, st.regs v⟩) :
    SExpr.evalBV (envReader env) p.toSExpr = (runBlock st (lowerArith id p)).regs p.dst := by
  cases p with
  | mk dst a op b =>
    have hRa : envReader env a = st.regs a := by simp only [envReader, hagree a ha]
    have hRb : envReader env b = st.regs b := by simp only [envReader, hagree b hbt]
    rw [runBlock_lowerArith_id_dst dst a b op st hb]
    cases op <;> simp only [ArithSrc.toSExpr, SExpr.evalBV, hRa, hRb]

/-- **Generalized single-step tie.**  For ANY input env agreeing with `regEnv st`
    on non-temp names (not just `regEnv st` itself), `semScalar` succeeds on
    `ArithSrc.toLowCT p` and its result agrees with `regEnv` of the machine
    post-state on every non-temp name — provided `p`'s source reads `a`, `b` are
    non-temp (so the fresh SExpr temps don't collide with them).  The threading
    lemma behind the block induction: it lets the tail statement start from the
    previous statement's (temporary-polluted) output env, since that env still
    agrees with the machine register view on non-temp names. -/
theorem arith_step_tie_gen (p : ArithSrc) (st : JState 64) (env : SEnvScalar)
    (hagree : ∀ v, ¬ isTmpName v → env v = some ⟨.sword 64, st.regs v⟩)
    (ha : ¬ isTmpName p.a) (hbt : ¬ isTmpName p.b) (hb : p.b ≠ p.dst) :
    ∃ env1, semScalar (ArithSrc.toLowCT p) env = some env1
      ∧ ∀ v, ¬ isTmpName v →
          env1 v = some ⟨.sword 64, (runBlock st (lowerArith id p)).regs v⟩ := by
  have hval := evalBV_toSExpr_eq_machine p st env ha hbt hb hagree
  have hoth : ∀ v, v ≠ p.dst → (runBlock st (lowerArith id p)).regs v = st.regs v :=
    fun v hvd => runBlock_lowerArith_id_other p st v hvd
  cases p with
  | mk dst a op b =>
    have hEa : envReadU64 env a = some (st.regs a) := by simp only [envReadU64, hagree a ha]
    have hEb : envReadU64 env b = some (st.regs b) := by simp only [envReadU64, hagree b hbt]
    cases op <;>
      · simp only [ArithSrc.toSExpr] at hval
        simp only [ArithSrc.toLowCT, ArithSrc.toSExpr, semScalar, semLowerSExpr, binNode,
          hEa, hEb]
        refine ⟨_, rfl, ?_⟩
        intro v hv
        by_cases hvd : v = dst
        · subst hvd
          simp only [SEnvScalar.upd, if_true, hval]
        · have hvt : v ≠ tmpName 0 := fun hh => hv ⟨0, hh⟩
          simp only [SEnvScalar.upd, if_neg hvd, if_neg hvt, hagree v hv, hoth v hvd]

/-- Generalized block tie, threaded over an arbitrary starting env that agrees
    with `regEnv st` on non-temp names.  Induction on `ps`: the head statement
    steps via `arith_step_tie_gen` (whose output env again agrees with the
    machine register view on non-temp names), feeding the tail's induction
    hypothesis; the machine side composes via `lowerSeq_cons` + `runBlock_append`.
    -/
theorem arith_seq_tie_gen (ps : List ArithSrc)
    (hwf : ∀ p ∈ ps, p.b ≠ p.dst)
    (hclean : ∀ p ∈ ps, ¬ isTmpName p.a ∧ ¬ isTmpName p.b) :
    ∀ (st : JState 64) (env : SEnvScalar),
      (∀ v, ¬ isTmpName v → env v = some ⟨.sword 64, st.regs v⟩) →
      ∃ env', semScalar (ArithSrc.seqToLowCT ps) env = some env'
        ∧ ∀ v, ¬ isTmpName v → env' v = regEnv (runBlock st (lowerSeq id ps)) v := by
  induction ps with
  | nil =>
      intro st env hag
      refine ⟨env, ?_, ?_⟩
      · simp only [ArithSrc.seqToLowCT_nil, semScalar]
      · intro v hv
        simp only [lowerSeq_nil, runBlock_nil, regEnv]
        exact hag v hv
  | cons p ps ih =>
      intro st env hag
      have hbp : p.b ≠ p.dst := hwf p (List.mem_cons_self ..)
      have hcp := hclean p (List.mem_cons_self ..)
      obtain ⟨env1, hsem1, hro1⟩ := arith_step_tie_gen p st env hag hcp.1 hcp.2 hbp
      obtain ⟨env', hsem', hro'⟩ :=
        ih (fun q hq => hwf q (List.mem_cons_of_mem _ hq))
          (fun q hq => hclean q (List.mem_cons_of_mem _ hq))
          (runBlock st (lowerArith id p)) env1 hro1
      refine ⟨env', ?_, ?_⟩
      · simp only [ArithSrc.seqToLowCT_cons, semScalar, hsem1]
        exact hsem'
      · intro v hv
        rw [hro' v hv, lowerSeq_cons, runBlock_append]

/-- **The block-level non-temp middle tie.**  For a source-clean, well-formed
    straight-line block `ps : List ArithSrc`, the folded scalar machine
    `semScalar (ArithSrc.seqToLowCT ps) (regEnv st)` succeeds and agrees with the
    machine register view `regEnv (runBlock st (lowerSeq id ps))` of the lowered
    block on every non-temp name.  The block extension of
    `arith_middle_tie_nonTmp`, specializing `arith_seq_tie_gen` at the total
    register view `regEnv st` (which agrees with itself everywhere). -/
theorem arith_middle_tie_seq_nonTmp (ps : List ArithSrc)
    (hwf : ∀ p ∈ ps, p.b ≠ p.dst)
    (hclean : ∀ p ∈ ps, ¬ isTmpName p.a ∧ ¬ isTmpName p.b)
    (st : JState 64) :
    ∃ env', semScalar (ArithSrc.seqToLowCT ps) (regEnv st) = some env'
      ∧ ∀ v, ¬ isTmpName v →
          env' v = regEnv (runBlock st (lowerSeq id ps)) v :=
  arith_seq_tie_gen ps hwf hclean st (regEnv st) (fun _ _ => rfl)

end CatCrypt.Crypto.SecureCompilation.Ascent
