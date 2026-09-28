/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.CT.LowCTLeakage
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTForCT

/-!
# Constant time from `LowCT` to owned structured machine code

A lowering of a `LowCT` fragment with control flow to the owned structured machine
blocks `MachineConstantTime.OwnedCF`, and the preservation of constant time from
the source model of `CT/LowCTLeakage.lean` (`RustExecLeak`, `LowCTConstantTime`)
to the machine model of `CT/Leakage.lean` (`cfLeakCT`).

* `CFSrc` is the fragment: two-operand scalar arithmetic (`ArithSrc`), sequence,
  a conditional `RIfNz`, and a counted loop `RFor x n` with a literal trip count.
  `CFSrc.toLowCT` embeds it in `LowCT`.
* `lowerCF ρ` lowers it to `OwnedCF 64`: arithmetic by
  `LowCTToJInstrCT.lowerArith`, the conditional to `ifPub (ρ g)`, the loop to
  `loop n` over a body that copies the counter register `ctr` into `ρ x`, runs the
  lowered body and increments `ctr`.
* `srcDen` and `srcLeak` are the source post-state and trace;
  `srcRun` shows they form a `RustExecLeak` run under `LowCTLeakModel.owned`,
  and `srcRun_det` that every run of `c.toLowCT` has this post-state and trace.
* `lowerCF_leak` is the leak transformer: from states related by
  `StateMatch ρ`, the machine trace `cfLeakCT .doitm` of the lowering equals the
  source trace, provided every guard value the source run tests is below `2^64`
  (`InRange`). `lowerCF_leak_of_run` states it for an arbitrary run.
* `lowct_to_machine_ct` derives machine `ConstantTime` from
  `LowCTConstantTime`, for machine states agreeing on the public registers whose
  source images satisfy `InRange`; `lowct_to_machine_ct_guardFree` drops the
  range condition on conditional-free programs.
* `lowerArith_mnem` states that the arithmetic lowering emits `MOV` followed by the
  mnemonic `sexprMnem` assigns to the source expression.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CT.LowCTMachine

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTForCT (movImm evalInstr_movImm)
open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. The fragment and its lowering -/

/-- The source fragment: scalar arithmetic, sequence, a conditional on a scalar
    guard, and a loop with literal trip count `n` over the index `x`; `ctr` names
    the machine counter register of the loop. -/
inductive CFSrc where
  | skip
  | arith (p : ArithSrc)
  | seq (a b : CFSrc)
  | ifNz (g : String) (thenB elseB : CFSrc)
  | forLit (x ctr : String) (n : Nat) (body : CFSrc)

/-- The embedding into `LowCT`. -/
def CFSrc.toLowCT : CFSrc → LowCT
  | .skip => .RSkip
  | .arith p => p.toLowCT
  | .seq a b => .RSeq a.toLowCT b.toLowCT
  | .ifNz g t e => .RIfNz g t.toLowCT e.toLowCT
  | .forLit x _ n body => .RFor x n body.toLowCT

/-- The machine body of one loop iteration: `ρ x := ctr`, the lowered body,
    `ctr := ctr + 1`. -/
def loopBody (ρ : RegMap) (x ctr : String) (body : OwnedCF 64) : OwnedCF 64 :=
  .seq (.straight [.mov (ρ x) (.reg ctr)]) (.seq body (.straight [.add ctr (.imm 1)]))

/-- The lowering to owned structured machine code. -/
def lowerCF (ρ : RegMap) : CFSrc → OwnedCF 64
  | .skip => .straight []
  | .arith p => .straight (lowerArith ρ p)
  | .seq a b => .seq (lowerCF ρ a) (lowerCF ρ b)
  | .ifNz g t e => .ifPub (ρ g) (lowerCF ρ t) (lowerCF ρ e)
  | .forLit x ctr n body =>
      .seq (.straight [movImm ctr 0]) (.loop n (loopBody ρ x ctr (lowerCF ρ body)))

/-- The counter registers of the loops of a program. -/
def CFSrc.ctrs : CFSrc → List String
  | .skip | .arith _ => []
  | .seq a b => a.ctrs ++ b.ctrs
  | .ifNz _ t e => t.ctrs ++ e.ctrs
  | .forLit _ ctr _ body => ctr :: body.ctrs

/-- Register-allocation side conditions: the second operand of an arithmetic
    statement is not its destination, and each loop counter lies outside the
    image of `ρ` and is not the counter of a nested loop. -/
def CFSrc.WF (ρ : RegMap) : CFSrc → Prop
  | .skip => True
  | .arith p => p.b ≠ p.dst
  | .seq a b => a.WF ρ ∧ b.WF ρ
  | .ifNz _ t e => t.WF ρ ∧ e.WF ρ
  | .forLit _ ctr _ body => (∀ v, ρ v ≠ ctr) ∧ ctr ∉ body.ctrs ∧ body.WF ρ

/-- Whether a program has no conditional. -/
def CFSrc.guardFree : CFSrc → Bool
  | .skip | .arith _ => true
  | .seq a b => a.guardFree && b.guardFree
  | .ifNz _ _ _ => false
  | .forLit _ _ _ body => body.guardFree

/-! ## 2. Source post-state and trace -/

/-- `k` loop iterations starting at index `i`: each sets `x` to the index, then
    applies `f`. -/
def iterDen (x : String) (f : RustState → RustState) : Nat → Nat → RustState → RustState
  | 0, _, rs => rs
  | k + 1, i, rs => iterDen x f k (i + 1) (f (rsSetScalar rs x i))

/-- The trace of `k` loop iterations starting at index `i`. -/
def iterTrace (x : String) (f : RustState → RustState) (l : RustState → List CTLeak) :
    Nat → Nat → RustState → List CTLeak
  | 0, _, _ => []
  | k + 1, i, rs => l (rsSetScalar rs x i) ++ iterTrace x f l k (i + 1) (f (rsSetScalar rs x i))

/-- A predicate on the entry state of each of `k` loop iterations. -/
def iterAll (x : String) (f : RustState → RustState) (P : RustState → Prop) :
    Nat → Nat → RustState → Prop
  | 0, _, _ => True
  | k + 1, i, rs => P (rsSetScalar rs x i) ∧ iterAll x f P k (i + 1) (f (rsSetScalar rs x i))

/-- The source post-state. -/
def srcDen : CFSrc → RustState → RustState
  | .skip, rs => rs
  | .arith p, rs => rsSetScalar rs p.dst (p.toSExpr.evalState rs)
  | .seq a b, rs => srcDen b (srcDen a rs)
  | .ifNz g t e, rs => if rs.rsScalar g = 0 then srcDen e rs else srcDen t rs
  | .forLit x _ n body, rs => iterDen x (srcDen body) n 0 rs

/-- The source leakage trace under `LowCTLeakModel.owned`. -/
def srcLeak : CFSrc → RustState → List CTLeak
  | .skip, _ => []
  | .arith p, rs => sexprLeak .owned rs p.toSExpr
  | .seq a b, rs => srcLeak a rs ++ srcLeak b (srcDen a rs)
  | .ifNz g t e, rs =>
      if rs.rsScalar g = 0 then .branch false :: srcLeak e rs else .branch true :: srcLeak t rs
  | .forLit x _ n body, rs => iterTrace x (srcDen body) (srcLeak body) n 0 rs

/-- Every guard value the source run tests is below `2^64`. -/
def InRange : CFSrc → RustState → Prop
  | .skip, _ => True
  | .arith _, _ => True
  | .seq a b, rs => InRange a rs ∧ InRange b (srcDen a rs)
  | .ifNz g t e, rs =>
      rs.rsScalar g < 2 ^ 64 ∧ (if rs.rsScalar g = 0 then InRange e rs else InRange t rs)
  | .forLit x _ n body, rs => iterAll x (srcDen body) (InRange body) n 0 rs

theorem iterAll_of_forall (x : String) (f : RustState → RustState) (P : RustState → Prop)
    (hP : ∀ rs, P rs) : ∀ k i rs, iterAll x f P k i rs := by
  intro k
  induction k with
  | zero => intro _ _; trivial
  | succ k ih => intro i rs; exact ⟨hP _, ih _ _⟩

theorem inRange_of_guardFree : ∀ (c : CFSrc), c.guardFree = true → ∀ rs, InRange c rs
  | .skip, _, _ => trivial
  | .arith _, _, _ => trivial
  | .seq a b, h, rs => by
    simp only [CFSrc.guardFree, Bool.and_eq_true] at h
    exact ⟨inRange_of_guardFree a h.1 rs, inRange_of_guardFree b h.2 _⟩
  | .ifNz _ _ _, h, _ => by simp [CFSrc.guardFree] at h
  | .forLit x _ n body, h, rs =>
    iterAll_of_forall x _ _ (inRange_of_guardFree body h) n 0 rs

/-! ### 2.1 The source trace is the trace of `RustExecLeak` -/

theorem iterDen_succ (x : String) (f : RustState → RustState) :
    ∀ k i rs, iterDen x f (k + 1) i rs = f (rsSetScalar (iterDen x f k i rs) x (i + k)) := by
  intro k
  induction k with
  | zero => intro i rs; rfl
  | succ k ih =>
    intro i rs
    rw [iterDen, ih, iterDen, Nat.add_right_comm, Nat.add_assoc]

theorem iterTrace_succ (x : String) (f : RustState → RustState) (l : RustState → List CTLeak) :
    ∀ k i rs, iterTrace x f l (k + 1) i rs =
      iterTrace x f l k i rs ++ l (rsSetScalar (iterDen x f k i rs) x (i + k)) := by
  intro k
  induction k with
  | zero => intro i rs; simp [iterTrace, iterDen]
  | succ k ih =>
    intro i rs
    rw [iterTrace, ih, iterTrace, iterDen, List.append_assoc, Nat.add_right_comm,
      Nat.add_assoc]

theorem arith_limbFree (p : ArithSrc) : p.toSExpr.limbFree := ArithSrc.toSExpr_limbFree p

/-- The source post-state and trace form a `RustExecLeak` run. -/
theorem srcRun (N : Nat) (leafSpec : LeafSpec) :
    ∀ (c : CFSrc) (rs : RustState),
      RustExecLeak N leafSpec .owned c.toLowCT rs (srcLeak c rs) (srcDen c rs)
  | .skip, rs => .skip rs
  | .arith p, rs => .scalarSetExpr p.dst p.toSExpr rs
  | .seq a b, rs =>
    .seq _ _ _ _ _ _ _ (srcRun N leafSpec a rs) (srcRun N leafSpec b _)
  | .ifNz g t e, rs => by
    simp only [CFSrc.toLowCT, srcLeak, srcDen]
    by_cases hz : rs.rsScalar g = 0
    · rw [if_pos hz, if_pos hz]
      exact .ifFalse _ _ _ _ _ _ hz (srcRun N leafSpec e rs)
    · rw [if_neg hz, if_neg hz]
      exact .ifTrue _ _ _ _ _ _ _ rfl hz (srcRun N leafSpec t rs)
  | .forLit x ctr n body, rs => by
    simp only [CFSrc.toLowCT, srcLeak, srcDen]
    induction n with
    | zero => exact .forZero _ _ _
    | succ n ih =>
      rw [iterDen_succ, iterTrace_succ, Nat.zero_add]
      exact .forSucc _ _ _ _ _ _ _ _ ih (srcRun N leafSpec body _)

/-- Every run of `c.toLowCT` has the post-state `srcDen c rs` and the trace
    `srcLeak c rs`. -/
theorem srcRun_det (N : Nat) (leafSpec : LeafSpec) :
    ∀ (c : CFSrc) (rs : RustState) (t : List CTLeak) (rs' : RustState),
      RustExecLeak N leafSpec .owned c.toLowCT rs t rs' → t = srcLeak c rs ∧ rs' = srcDen c rs
  | .skip, rs, t, rs', h => by cases h; exact ⟨rfl, rfl⟩
  | .arith p, rs, t, rs', h => by cases h; exact ⟨rfl, rfl⟩
  | .seq a b, rs, t, rs', h => by
    cases h with
    | seq _ _ _ r1 _ t1 t2 h1 h2 =>
      obtain ⟨rfl, rfl⟩ := srcRun_det N leafSpec a rs t1 r1 h1
      obtain ⟨rfl, rfl⟩ := srcRun_det N leafSpec b _ t2 rs' h2
      exact ⟨rfl, rfl⟩
  | .ifNz g th el, rs, t, rs', h => by
    cases h with
    | ifTrue _ _ _ _ _ v tr hv hv0 hb =>
      obtain ⟨rfl, rfl⟩ := srcRun_det N leafSpec th rs tr rs' hb
      have hz : ¬ rs.rsScalar g = 0 := hv ▸ hv0
      simp only [srcLeak, srcDen, if_neg hz]
      exact ⟨trivial, trivial⟩
    | ifFalse _ _ _ _ _ tr hv hb =>
      obtain ⟨rfl, rfl⟩ := srcRun_det N leafSpec el rs tr rs' hb
      simp only [srcLeak, srcDen, if_pos hv]
      exact ⟨trivial, trivial⟩
  | .forLit x ctr n body, rs, t, rs', h => by
    simp only [CFSrc.toLowCT] at h
    simp only [srcLeak, srcDen]
    induction n generalizing t rs' with
    | zero => cases h; exact ⟨rfl, rfl⟩
    | succ n ih =>
      cases h with
      | forSucc _ _ _ _ r1 _ t1 t2 h1 h2 =>
        obtain ⟨rfl, rfl⟩ := ih t1 r1 h1
        obtain ⟨rfl, rfl⟩ := srcRun_det N leafSpec body _ t2 rs' h2
        rw [iterDen_succ, iterTrace_succ, Nat.zero_add]
        exact ⟨rfl, rfl⟩

/-! ## 3. The machine side -/

/-- The owned mnemonic of the arithmetic instruction is `sexprMnem` of the source
    expression: the lowering emits `MOV` and then that mnemonic. -/
theorem lowerArith_mnem (ρ : RegMap) (p : ArithSrc) :
    (lowerArith ρ p).map JInstr.mnem = X86Mnem.mov :: (sexprMnem p.toSExpr).toList := by
  cases p with
  | mk dst a op b => cases op <;> rfl

/-- The arithmetic lowering has an empty machine trace under DOITM. -/
theorem blockLeakCT_lowerArith (ρ : RegMap) (p : ArithSrc) (s : JState 64) :
    blockLeakCT .doitm s (lowerArith ρ p) = [] := by
  cases p with
  | mk dst a op b => cases op <;> rfl

/-- The arithmetic source trace is empty under the owned model. -/
theorem sexprLeak_arith (p : ArithSrc) (rs : RustState) :
    sexprLeak .owned rs p.toSExpr = [] := by
  cases p with
  | mk dst a op b => cases op <;> rfl

theorem cfExec_straight_snd (s : JState 64) (b : List (JInstr 64)) :
    (cfExec s (.straight b)).2 = runBlock s b := by
  rw [cfExec]

theorem cfExec_seq_snd (s : JState 64) (a b : OwnedCF 64) :
    (cfExec s (.seq a b)).2 = (cfExec (cfExec s a).2 b).2 := by
  rw [cfExec]

theorem cfExec_loop_snd (s : JState 64) (n : Nat) (b : OwnedCF 64) :
    (cfExec s (.loop n b)).2 = (cfLoop n b s).2 := by
  rw [cfExec]

theorem cfLoop_succ_snd (s : JState 64) (n : Nat) (b : OwnedCF 64) :
    (cfLoop (n + 1) b s).2 = (cfLoop n b (cfExec s b).2).2 := by
  rw [cfLoop]

theorem cfExec_ifPub_snd (s : JState 64) (g : String) (t e : OwnedCF 64) :
    (cfExec s (.ifPub g t e)).2 = if s.get g = 0 then (cfExec s e).2 else (cfExec s t).2 := by
  rw [cfExec]
  split <;> rfl

theorem evalInstr_mov_reg (s : JState 64) (d r : String) :
    evalInstr s (.mov d (.reg r)) = s.setReg d (s.get r) := by
  simp [evalInstr, x86_MOV, JOperand.eval]

theorem evalInstr_add_imm_get (s : JState 64) (d r : String) (n : Nat) :
    (evalInstr s (.add d (.imm n))).get r = if r = d then s.get d + BitVec.ofNat 64 n
      else s.get r := by
  by_cases h : r = d
  · subst h; simp [evalInstr, x86_ADD, rflags_of_aluop, JState.writeB5W, JState.get]
  · simp [evalInstr, x86_ADD, rflags_of_aluop, JState.writeB5W, JState.get, h]

/-- A register outside the image of `ρ` and distinct from every loop counter of
    `c` keeps its value across the lowered program. -/
theorem lowerCF_preserves (ρ : RegMap) (r : String) (hr : ∀ v, ρ v ≠ r) :
    ∀ (c : CFSrc), r ∉ c.ctrs → ∀ s, (cfExec s (lowerCF ρ c)).2.get r = s.get r
  | .skip, _, s => by rw [lowerCF, cfExec_straight_snd]; rfl
  | .arith p, _, s => by
    rw [lowerCF, cfExec_straight_snd]
    simp only [lowerArith, runBlock_cons, runBlock_nil]
    have hd : r ≠ ρ p.dst := fun h => hr p.dst h.symm
    rw [ArithOp.toJInstr_get_other _ _ _ _ _ hd, evalInstr_mov_reg,
      JState.get_setReg_other _ _ _ _ hd]
  | .seq a b, h, s => by
    simp only [CFSrc.ctrs, List.mem_append, not_or] at h
    rw [lowerCF, cfExec_seq_snd, lowerCF_preserves ρ r hr b h.2,
      lowerCF_preserves ρ r hr a h.1]
  | .ifNz g t e, h, s => by
    simp only [CFSrc.ctrs, List.mem_append, not_or] at h
    rw [lowerCF, cfExec_ifPub_snd]
    split
    · exact lowerCF_preserves ρ r hr e h.2 s
    · exact lowerCF_preserves ρ r hr t h.1 s
  | .forLit x ctr n body, h, s => by
    simp only [CFSrc.ctrs, List.mem_cons, not_or] at h
    have hbody := lowerCF_preserves ρ r hr body h.2
    rw [lowerCF, cfExec_seq_snd, cfExec_loop_snd]
    have hstep : ∀ s', (cfExec s' (loopBody ρ x ctr (lowerCF ρ body))).2.get r = s'.get r := by
      intro s'
      have hx : r ≠ ρ x := fun h' => hr x h'.symm
      rw [loopBody, cfExec_seq_snd, cfExec_seq_snd, cfExec_straight_snd, cfExec_straight_snd]
      simp only [runBlock_cons, runBlock_nil]
      rw [evalInstr_add_imm_get, if_neg h.1, hbody, evalInstr_mov_reg,
        JState.get_setReg_other _ _ _ _ hx]
    have hloop : ∀ k s', (cfLoop k (loopBody ρ x ctr (lowerCF ρ body)) s').2.get r = s'.get r := by
      intro k
      induction k with
      | zero => intro s'; rw [cfLoop]
      | succ k ih => intro s'; rw [cfLoop_succ_snd, ih, hstep]
    rw [hloop, cfExec_straight_snd]
    simp only [runBlock_cons, runBlock_nil, evalInstr_movImm]
    exact JState.get_setReg_other _ _ _ _ h.1

theorem ofNat_eq_zero_iff_of_lt (v : Nat) (hv : v < 2 ^ 64) :
    BitVec.ofNat 64 v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    rwa [Nat.mod_eq_of_lt hv] at this
  · rintro rfl; rfl

/-- The leak transformer and the state simulation: from states related by
    `StateMatch ρ`, the machine post-state of the lowering is related to the
    source post-state, and the machine trace equals the source trace. -/
theorem lowerCF_sim (ρ : RegMap) (hρ : Function.Injective ρ) :
    ∀ (c : CFSrc), c.WF ρ → ∀ rs js, StateMatch ρ rs js → InRange c rs →
      StateMatch ρ (srcDen c rs) (cfExec js (lowerCF ρ c)).2 ∧
        cfLeakCT .doitm js (lowerCF ρ c) = srcLeak c rs
  | .skip, _, rs, js, hm, _ => by
    refine ⟨?_, rfl⟩
    rw [lowerCF, cfExec_straight_snd]; exact hm
  | .arith p, hwf, rs, js, hm, _ => by
    refine ⟨?_, ?_⟩
    · rw [lowerCF, cfExec_straight_snd, srcDen,
        SExpr.evalState_eq_eval rs _ (arith_limbFree p)]
      exact lowerArith_denote ρ p rs js hρ hwf hm
    · rw [lowerCF, cfLeakCT, blockLeakCT_lowerArith, srcLeak, sexprLeak_arith]
  | .seq a b, hwf, rs, js, hm, hin => by
    obtain ⟨hma, hla⟩ := lowerCF_sim ρ hρ a hwf.1 rs js hm hin.1
    obtain ⟨hmb, hlb⟩ := lowerCF_sim ρ hρ b hwf.2 _ _ hma hin.2
    refine ⟨?_, ?_⟩
    · rw [lowerCF, cfExec_seq_snd]; exact hmb
    · rw [lowerCF, cfLeakCT, hla, hlb, srcLeak]
  | .ifNz g t e, hwf, rs, js, hm, hin => by
    obtain ⟨hlt, hin'⟩ := hin
    have hg : js.get (ρ g) = 0 ↔ rs.rsScalar g = 0 := by
      rw [hm g]; exact ofNat_eq_zero_iff_of_lt _ hlt
    by_cases hz : rs.rsScalar g = 0
    · have hjz : js.get (ρ g) = 0 := hg.2 hz
      rw [if_pos hz] at hin'
      obtain ⟨hme, hle⟩ := lowerCF_sim ρ hρ e hwf.2 rs js hm hin'
      refine ⟨?_, ?_⟩
      · rw [lowerCF, cfExec_ifPub_snd, if_pos hjz, srcDen, if_pos hz]; exact hme
      · rw [lowerCF, cfLeakCT, if_pos hjz, srcLeak, if_pos hz, hle]
    · have hjz : ¬ js.get (ρ g) = 0 := fun h => hz (hg.1 h)
      rw [if_neg hz] at hin'
      obtain ⟨hmt, hlt'⟩ := lowerCF_sim ρ hρ t hwf.1 rs js hm hin'
      refine ⟨?_, ?_⟩
      · rw [lowerCF, cfExec_ifPub_snd, if_neg hjz, srcDen, if_neg hz]; exact hmt
      · rw [lowerCF, cfLeakCT, if_neg hjz, srcLeak, if_neg hz, hlt']
  | .forLit x ctr n body, hwf, rs, js, hm, hin => by
    obtain ⟨hctrρ, hctrb, hwfb⟩ := hwf
    have ih := lowerCF_sim ρ hρ body hwfb
    have hpres := lowerCF_preserves ρ ctr hctrρ body hctrb
    set B := loopBody ρ x ctr (lowerCF ρ body) with hB
    -- one iteration
    have hstep : ∀ (i : Nat) rs js, StateMatch ρ rs js → js.get ctr = BitVec.ofNat 64 i →
        InRange body (rsSetScalar rs x i) →
        StateMatch ρ (srcDen body (rsSetScalar rs x i)) (cfExec js B).2 ∧
          (cfExec js B).2.get ctr = BitVec.ofNat 64 (i + 1) ∧
          cfLeakCT .doitm js B = srcLeak body (rsSetScalar rs x i) := by
      intro i rs js hm hc hinb
      have hm1 : StateMatch ρ (rsSetScalar rs x i) (evalInstr js (.mov (ρ x) (.reg ctr))) := by
        intro v
        rw [evalInstr_mov_reg]
        by_cases hv : v = x
        · subst hv
          rw [JState.get_setReg_same, hc]
          simp [rsSetScalar]
        · have hvx : ρ v ≠ ρ x := fun h => hv (hρ h)
          rw [JState.get_setReg_other _ _ _ _ hvx]
          simp only [rsSetScalar, beq_eq_false_iff_ne.mpr hv, Bool.false_eq_true, if_false]
          exact hm v
      have hc1 : (evalInstr js (.mov (ρ x) (.reg ctr))).get ctr = BitVec.ofNat 64 i := by
        rw [evalInstr_mov_reg, JState.get_setReg_other _ _ _ _ (fun h => hctrρ x h.symm), hc]
      obtain ⟨hmb, hlb⟩ := ih _ _ hm1 hinb
      have hmid : (cfExec js (.straight [.mov (ρ x) (.reg ctr)])).2 =
          evalInstr js (.mov (ρ x) (.reg ctr)) := by
        rw [cfExec_straight_snd]; rfl
      refine ⟨?_, ?_, ?_⟩
      · rw [hB, loopBody, cfExec_seq_snd, cfExec_seq_snd, cfExec_straight_snd, hmid]
        simp only [runBlock_cons, runBlock_nil]
        intro v
        rw [evalInstr_add_imm_get, if_neg (hctrρ v)]
        exact hmb v
      · rw [hB, loopBody, cfExec_seq_snd, cfExec_seq_snd, cfExec_straight_snd, hmid]
        simp only [runBlock_cons, runBlock_nil]
        rw [evalInstr_add_imm_get, if_pos rfl, hpres, hc1]
        simp [BitVec.ofNat_add]
      · rw [hB, loopBody, cfLeakCT, cfLeakCT, cfLeakCT, cfLeakCT]
        have hmid' : (cfExec js (.straight [.mov (ρ x) (.reg ctr)])).2 =
            evalInstr js (.mov (ρ x) (.reg ctr)) := hmid
        rw [hmid', hlb]
        simp [blockLeakCT, instrLeakCT, instrLeak, JInstr.mnem, DoitRegime.leaksOperands,
          X86Mnem.timing]
    -- the loop
    have hloop : ∀ (k i : Nat) rs js, StateMatch ρ rs js → js.get ctr = BitVec.ofNat 64 i →
        iterAll x (srcDen body) (InRange body) k i rs →
        StateMatch ρ (iterDen x (srcDen body) k i rs) (cfLoop k B js).2 ∧
          iterLeak (fun s' => cfLeakCT .doitm s' B) (fun s' => (cfExec s' B).2) k js =
            iterTrace x (srcDen body) (srcLeak body) k i rs := by
      intro k
      induction k with
      | zero => intro i rs js hm _ _; rw [cfLoop]; exact ⟨hm, rfl⟩
      | succ k ihk =>
        intro i rs js hm hc hall
        obtain ⟨hm', hc', hl'⟩ := hstep i rs js hm hc hall.1
        obtain ⟨hmk, hlk⟩ := ihk (i + 1) _ _ hm' hc' hall.2
        refine ⟨?_, ?_⟩
        · rw [cfLoop_succ_snd, iterDen]; exact hmk
        · rw [iterLeak, iterTrace, hl', hlk]
    have hm0 : StateMatch ρ rs (evalInstr js (movImm ctr 0)) := by
      intro v
      rw [evalInstr_movImm, JState.get_setReg_other _ _ _ _ (hctrρ v)]
      exact hm v
    have hc0 : (evalInstr js (movImm ctr 0)).get ctr = BitVec.ofNat 64 0 := by
      rw [evalInstr_movImm, JState.get_setReg_same]
    obtain ⟨hmL, hlL⟩ := hloop n 0 rs _ hm0 hc0 hin
    have hpre : (cfExec js (.straight [movImm ctr 0])).2 = evalInstr js (movImm ctr 0) := by
      rw [cfExec_straight_snd]; rfl
    refine ⟨?_, ?_⟩
    · rw [lowerCF, cfExec_seq_snd, cfExec_loop_snd, hpre, srcDen]; exact hmL
    · rw [lowerCF, cfLeakCT, hpre, cfLeakCT, cfLeakCT, ← hB, hlL, srcLeak]
      simp [blockLeakCT, instrLeakCT, instrLeak, movImm, JInstr.mnem, DoitRegime.leaksOperands,
        X86Mnem.timing]

/-- The leak transformer: from states related by `StateMatch ρ`, the machine
    trace of the lowering is the source trace. -/
theorem lowerCF_leak (ρ : RegMap) (hρ : Function.Injective ρ) (c : CFSrc) (hwf : c.WF ρ)
    (rs : RustState) (js : JState 64) (hm : StateMatch ρ rs js) (hin : InRange c rs) :
    cfLeakCT .doitm js (lowerCF ρ c) = srcLeak c rs :=
  (lowerCF_sim ρ hρ c hwf rs js hm hin).2

/-- The leak transformer for an arbitrary run: the machine trace equals the trace
    `t` of any `RustExecLeak` run of the source program from a related state. -/
theorem lowerCF_leak_of_run (N : Nat) (leafSpec : LeafSpec) (ρ : RegMap)
    (hρ : Function.Injective ρ) (c : CFSrc) (hwf : c.WF ρ)
    (rs rs' : RustState) (t : List CTLeak) (js : JState 64) (hm : StateMatch ρ rs js)
    (hin : InRange c rs) (hrun : RustExecLeak N leafSpec .owned c.toLowCT rs t rs') :
    cfLeakCT .doitm js (lowerCF ρ c) = t := by
  rw [lowerCF_leak ρ hρ c hwf rs js hm hin, (srcRun_det N leafSpec c rs t rs' hrun).1]

/-! ## 4. Constant time -/

/-- The source state read off a machine state through `ρ`: each scalar slot `v`
    holds the value of register `ρ v`; no tower slot is bound. -/
def liftState (ρ : RegMap) (js : JState 64) : RustState :=
  { rsTower := fun _ => none, rsScalar := fun v => (js.get (ρ v)).toNat }

theorem liftState_match (ρ : RegMap) (js : JState 64) : StateMatch ρ (liftState ρ js) js := by
  intro v
  simp [liftState]

theorem liftState_pubEq (ρ : RegMap) (lt : LevelTable) (pub : PubPred)
    (hpub : ∀ x, lt x = .Public → pub (ρ x) = true) (js₁ js₂ : JState 64)
    (hag : agreePub pub js₁ js₂) : PubEqRS lt (liftState ρ js₁) (liftState ρ js₂) := by
  intro x hx
  refine ⟨?_, rfl⟩
  simp only [liftState]
  rw [hag (ρ x) (hpub x hx)]

/-- Constant time from `LowCT` to owned machine code. If the source program is
    constant time for the split `lt` in the owned leakage model, its lowering is
    constant time in the machine model under DOITM, for machine states agreeing on
    the public registers `pub` (which contain the image of every public slot)
    whose source images test only guard values below `2^64`. -/
theorem lowct_to_machine_ct (N : Nat) (leafSpec : LeafSpec) (lt : LevelTable)
    (pub : PubPred) (ρ : RegMap) (hρ : Function.Injective ρ) (c : CFSrc) (hwf : c.WF ρ)
    (hpub : ∀ x, lt x = .Public → pub (ρ x) = true)
    (hsrc : LowCTConstantTime N leafSpec .owned lt c.toLowCT) :
    ConstantTime
      (fun js₁ js₂ : JState 64 => agreePub pub js₁ js₂ ∧
        InRange c (liftState ρ js₁) ∧ InRange c (liftState ρ js₂))
      (fun js => cfLeakCT .doitm js (lowerCF ρ c)) := by
  rintro js₁ js₂ ⟨hag, h₁, h₂⟩
  simp only
  rw [lowerCF_leak ρ hρ c hwf _ js₁ (liftState_match ρ js₁) h₁,
    lowerCF_leak ρ hρ c hwf _ js₂ (liftState_match ρ js₂) h₂]
  exact hsrc _ _ _ _ (liftState_pubEq ρ lt pub hpub js₁ js₂ hag)
    ⟨_, srcRun N leafSpec c _⟩ ⟨_, srcRun N leafSpec c _⟩

/-- Constant time from `LowCT` to owned machine code for a program without
    conditionals (straight-line code and counted loops): no range condition. -/
theorem lowct_to_machine_ct_guardFree (N : Nat) (leafSpec : LeafSpec) (lt : LevelTable)
    (pub : PubPred) (ρ : RegMap) (hρ : Function.Injective ρ) (c : CFSrc) (hwf : c.WF ρ)
    (hgf : c.guardFree = true)
    (hpub : ∀ x, lt x = .Public → pub (ρ x) = true)
    (hsrc : LowCTConstantTime N leafSpec .owned lt c.toLowCT) :
    ConstantTime (fun js₁ js₂ : JState 64 => agreePub pub js₁ js₂)
      (fun js => cfLeakCT .doitm js (lowerCF ρ c)) := fun js₁ js₂ hag =>
  lowct_to_machine_ct N leafSpec lt pub ρ hρ c hwf hpub hsrc js₁ js₂
    ⟨hag, inRange_of_guardFree c hgf _, inRange_of_guardFree c hgf _⟩

/-- The single arithmetic statement of `LowCTToJInstrCT.lowerArith_source_to_machine_CT`,
    with source constant time in the `CTP-1` model as the premise and machine
    constant time in the `CTP-1` model as the conclusion. -/
theorem lowerArith_source_to_machine_CT' (N : Nat) (leafSpec : LeafSpec) (lt : LevelTable)
    (pub : PubPred) (ρ : RegMap) (hρ : Function.Injective ρ) (p : ArithSrc) (hb : p.b ≠ p.dst)
    (hpub : ∀ x, lt x = .Public → pub (ρ x) = true)
    (hsrc : LowCTConstantTime N leafSpec .owned lt p.toLowCT) :
    MachineCT .doitm pub (lowerArith ρ p) := fun js₁ js₂ hag =>
  lowct_to_machine_ct_guardFree N leafSpec lt pub ρ hρ (.arith p) hb rfl hpub hsrc js₁ js₂ hag

/-- The lowering of a conditional on the secret scalar `k` is not constant time
    at the machine: two states that differ only in `k` take different branches. -/
theorem secretGuard_lowered_not_ct :
    ¬ ConstantTime
      (fun js₁ js₂ : JState 64 => agreePub (fun r => r != "k") js₁ js₂ ∧
        InRange (.ifNz "k" .skip .skip) (liftState id js₁) ∧
        InRange (.ifNz "k" .skip .skip) (liftState id js₂))
      (fun js => cfLeakCT .doitm js (lowerCF id (.ifNz "k" .skip .skip))) := by
  intro h
  have hin : ∀ js : JState 64, InRange (.ifNz "k" .skip .skip) (liftState id js) := by
    intro js
    refine ⟨(js.get "k").isLt, ?_⟩
    split <;> trivial
  have := h zeroState kOneState ⟨zero_kOne_agree _ rfl, hin _, hin _⟩
  simp [lowerCF, cfLeakCT, zeroState, kOneState, JState.get] at this

end CatCrypt.Crypto.SecureCompilation.CT.LowCTMachine
