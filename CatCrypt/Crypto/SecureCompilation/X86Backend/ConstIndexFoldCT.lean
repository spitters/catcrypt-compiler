/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold
public import CatCrypt.Crypto.SecureCompilation.CT.Leakage

/-!
# Leakage of the constant-index fold and the dead-move elimination

The machine model of `ConstIndexFold` is `Jasmin.runBlock` over the block
`gatherPrinted` produces from an `Lcmd` body. This module states the leakage of
the two passes in that model, with the observation trace `CT.blockLeakCT` of
`CT/Leakage.lean` (memory addresses, and the data operands of the instructions a
hardware regime makes observable).

* `foldCore_leak`: from every state the analysis environment describes, the
  folded body's gathered block has the leakage trace of the input's block. A
  folded access `loadMem d B (sc·v)` issues the address `(B, sc·v)`, which is the
  address `loadMemIdx d B x sc` issues when `x` holds `v`.
* `gatherPrinted_constIndexFoldBody_leak`: the same for `constIndexFoldBody`, from
  every state and under every regime.
* `dropDeadCore_leak`, `gatherPrinted_dropDeadImmBody_leak`: removing an immediate
  move to a register that is overwritten before it is read leaves the trace
  unchanged under a regime in which `mov` is quiet (`DoitRegime.doitm`). The
  removed move issues no address; under `DoitRegime.unguaranteed` it would issue
  a `vt` event with its immediate.
* `constIndexFoldBody_machineCT`, `dropDeadImmBody_machineCT`,
  `foldDrop_machineCT`: constant time of the gathered block (`CT.MachineCT`) is
  preserved by the fold, by the elimination, and by the two in sequence.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFoldCT

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime (PubPred instrLeak)
open CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrGatherExtended (isLret)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold
open CatCrypt.Crypto.SecureCompilation.CT

/-! ## 1. Leakage of a concatenation -/

theorem blockLeakCT_append' {w : Nat} (r : DoitRegime) (s : JState w)
    (l₁ l₂ : List (JInstr w)) :
    blockLeakCT r s (l₁ ++ l₂) = blockLeakCT r s l₁ ++ blockLeakCT r (runBlock s l₁) l₂ := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons i is ih =>
      rw [List.cons_append, blockLeakCT_cons, blockLeakCT_cons, ih, runBlock_cons,
        List.append_assoc]

/-! ## 2. The fold -/

/-- A folded instruction lowers to a block with the leakage trace of the original
    block, from every state the environment describes. -/
theorem foldInstr_lower_leak (p : Nat × Nat × Nat) {ex : List String} {env : KEnv}
    {i : LinstrR} {js js' : List (JInstr 64)} (h : lowerPrinted p.1 p.2.1 p.2.2 i = some js)
    (h' : lowerPrinted p.1 p.2.1 p.2.2 (foldInstr ex env i) = some js') (r : DoitRegime)
    (s : JState 64) (hs : KEnv.Holds s env) :
    blockLeakCT r s js' = blockLeakCT r s js := by
  unfold foldInstr at h'
  split at h'
  · rw [h] at h'
    cases h'
    rfl
  cases hf : foldTarget? env i with
  | none =>
      rw [hf] at h'
      rw [Option.getD_none, h] at h'
      cases h'
      rfl
  | some i' =>
      rw [hf, Option.getD_some] at h'
      rcases foldTarget?_spec hf with
        ⟨d, B, x, sc, v, rfl, rfl, hx⟩ | ⟨d, B, x, sc, vn, v, rfl, rfl, hx⟩ |
          ⟨d, x, v, rfl, rfl, hx⟩
      · rw [lowerPrinted_loadIdx] at h
        rw [lowerPrinted_load] at h'
        cases h
        cases h'
        have hv : s.regs x = v := hs x v hx
        simp [blockLeakCT, instrLeakCT, instrLeak, JInstr.mnem, JInstr.dataArgs,
          JState.loadIdx, hv]
      · rw [lowerPrinted_storeIdx] at h
        rw [lowerPrinted_store] at h'
        cases h
        cases h'
        have hv : s.get x = v := hs x v hx
        simp only [blockLeakCT_cons, blockLeakCT_nil, instrLeakCT, instrLeak, JInstr.mnem,
          JInstr.dataArgs]
        rw [hv]
        rfl
      · rw [lowerPrinted_movReg] at h
        rw [lowerPrinted_movImm] at h'
        cases h
        cases h'
        have hv : s.regs x = v := hs x v hx
        simp [blockLeakCT, instrLeakCT, instrLeak, JInstr.mnem, JInstr.dataArgs,
          JOperand.eval, JState.get, hv]

/-- **Leakage of the fold at fixed frame parameters.** From every state the
    environment describes, the gathered block of the folded body has the leakage
    trace of the gathered block of the body. -/
theorem foldCore_leak (p : Nat × Nat × Nat) (ex : List String) (r : DoitRegime) :
    ∀ (body : Lcmd) (env : KEnv) (s : JState 64) (ls ls' : List (List (JInstr 64))),
      KEnv.Holds s env → gatherList p body = some ls →
      gatherList p (foldCore p ex env body) = some ls' →
      blockLeakCT r s ls'.flatten = blockLeakCT r s ls.flatten := by
  intro body
  induction body with
  | nil =>
      intro env s ls ls' _ h h'
      simp only [gatherList, foldCore, List.filter_nil, List.mapM_nil] at h h'
      cases h
      cases h'
      rfl
  | cons i is ih =>
      intro env s ls ls' hs h h'
      rw [foldCore, gatherList_cons] at h'
      rw [gatherList_cons] at h
      have hse := hs.foldEnv i.li_i is
      generalize foldEnv env i.li_i is = E at h' hse
      by_cases hr : isLret i = true
      · have hr' : isLret { i with li_i := foldInstr ex E i.li_i } = true := by
          rw [isLret_foldInstr]; exact hr
        rw [ite_eq_left hr] at h
        rw [ite_eq_left hr'] at h'
        exact ih (nextEnv p env i) s ls ls' (by
          simp only [nextEnv, hr, ite_true]; exact KEnv.Holds.nil s) h h'
      · have hr' : ¬ isLret { i with li_i := foldInstr ex E i.li_i } = true := by
          rw [isLret_foldInstr]; exact hr
        rw [ite_eq_right hr] at h
        rw [ite_eq_right hr'] at h'
        have hr0 : isLret i = false := by simpa using hr
        cases hi : lowerPrinted p.1 p.2.1 p.2.2 i.li_i with
        | none => simp [hi] at h
        | some js =>
            cases hrest : gatherList p is with
            | none => simp [hi, hrest] at h
            | some rest =>
                simp only [hi, hrest, Option.bind_some, Option.map_some,
                  Option.some.injEq] at h
                subst h
                cases hi' : lowerPrinted p.1 p.2.1 p.2.2 (foldInstr ex E i.li_i) with
                | none => simp [hi'] at h'
                | some js' =>
                    cases hrest' : gatherList p (foldCore p ex (nextEnv p env i) is) with
                    | none => simp [hi', hrest'] at h'
                    | some rest' =>
                        simp only [hi', hrest', Option.bind_some, Option.map_some,
                          Option.some.injEq] at h'
                        subst h'
                        obtain ⟨js'', hj'', hrun⟩ := foldInstr_lower p (ex := ex) (env := E) hi
                        rw [hi'] at hj''
                        cases hj''
                        have henv : nextEnv p env i =
                            (stepKs env js).killAll (narrowImmDsts i.li_i) := by
                          simp [nextEnv, hr0, hi]
                        simp only [List.flatten_cons, blockLeakCT_append',
                          foldInstr_lower_leak p hi hi' r s hse, hrun s hse]
                        rw [ih (nextEnv p env i) (runBlock s js) rest rest'
                          (by rw [henv]; exact (hs.stepKs js).killAll _) hrest hrest']

/-- **Leakage of the fold.** If a body and its fold both gather, the two blocks
    have the same leakage trace from every state, under every regime. -/
theorem gatherPrinted_constIndexFoldBody_leak {body : Lcmd} {g g' : List (JInstr 64)}
    (h : gatherPrinted body = some g) (h' : gatherPrinted (constIndexFoldBody body) = some g')
    (r : DoitRegime) (s : JState 64) :
    blockLeakCT r s g' = blockLeakCT r s g := by
  unfold constIndexFoldBody at h'
  dsimp only at h'
  split at h'
  · rename_i hp
    rw [gatherPrinted_eq, Option.map_eq_some_iff] at h h'
    obtain ⟨ls, hls, rfl⟩ := h
    obtain ⟨ls', hls', rfl⟩ := h'
    rw [hp] at hls'
    exact foldCore_leak (bodyParams body) _ r body [] s ls ls' (KEnv.Holds.nil s) hls hls'
  · rw [h] at h'
    cases h'
    rfl

/-! ## 3. The dead-move elimination -/

/-- An instruction that is transparent to `x` or overwrites it without reading it
    has the same leakage from two states that agree off `x`. -/
theorem agreeOff_instrLeakCT_eq {x : String} {s t : JState 64} (h : AgreeOff x s t)
    {i : JInstr 64} (hi : transparentTo x i = true ∨ overwrites x i = true)
    (r : DoitRegime) : instrLeakCT r s i = instrLeakCT r t i := by
  obtain ⟨hf, hm, hr⟩ := h
  cases i with
  | mov d src =>
      cases src with
      | imm k => rfl
      | reg y =>
          have hy : y ≠ x := by
            rcases hi with hi | hi <;>
              simp only [transparentTo, overwrites, Bool.and_eq_true, bne_iff_ne, ne_eq,
                beq_iff_eq] at hi <;> tauto
          simp [instrLeakCT, instrLeak, JInstr.dataArgs, JOperand.eval, JState.get, hr y hy]
  | loadMem d B off =>
      simp [instrLeakCT, instrLeak, JInstr.dataArgs, JState.load, hm]
  | storeMem B off src =>
      cases src with
      | imm k => rfl
      | reg v =>
          have hv : v ≠ x := by
            rcases hi with hi | hi <;>
              simp only [transparentTo, overwrites, Bool.and_eq_true, bne_iff_ne,
                ne_eq] at hi <;> tauto
          simp [instrLeakCT, instrLeak, JInstr.dataArgs, JOperand.eval, JState.get, hr v hv]
  | _ => rcases hi with hi | hi <;> simp [transparentTo, overwrites] at hi

theorem scanBlock_leak {x : String} (r : DoitRegime) :
    ∀ {bs : List (JInstr 64)} {s t : JState 64}, scanBlock x bs ≠ some false →
      AgreeOff x s t → blockLeakCT r s bs = blockLeakCT r t bs
  | [], _, _, _, _ => rfl
  | i :: is, s, t, hb, h => by
      simp only [scanBlock] at hb
      rw [blockLeakCT_cons, blockLeakCT_cons]
      split at hb
      · rename_i ho
        rw [agreeOff_instrLeakCT_eq h (Or.inr ho) r, h.evalInstr_overwrites ho]
      · split at hb
        · rename_i _ ht
          rw [agreeOff_instrLeakCT_eq h (Or.inl ht) r,
            scanBlock_leak r (bs := is) hb (h.evalInstr_transparent ht)]
        · exact absurd rfl hb

/-- Along a body in which `x` is dead, two states that agree off `x` give the same
    leakage trace. -/
theorem deadAfter_leak (p : Nat × Nat × Nat) (x : String) (r : DoitRegime) :
    ∀ (body : Lcmd) (ls : List (List (JInstr 64))) (s t : JState 64),
      deadAfter p x body = true → gatherList p body = some ls → AgreeOff x s t →
      blockLeakCT r s ls.flatten = blockLeakCT r t ls.flatten := by
  intro body
  induction body with
  | nil => intro _ _ _ hd; simp [deadAfter] at hd
  | cons j js ih =>
      intro ls s t hd hg h
      by_cases hr : isLret j = true
      · simp [deadAfter, hr] at hd
      · rw [gatherList_cons, ite_eq_right hr] at hg
        simp only [deadAfter, hr, Bool.false_eq_true, ite_false] at hd
        cases hj : lowerPrinted p.1 p.2.1 p.2.2 j.li_i with
        | none => simp [hj] at hd
        | some bs =>
            rw [hj] at hg
            simp only [hj] at hd
            cases hrest : gatherList p js with
            | none => simp [hrest] at hg
            | some rest =>
                simp only [hrest, Option.bind_some, Option.map_some,
                  Option.some.injEq] at hg
                subst hg
                simp only [List.flatten_cons, blockLeakCT_append']
                cases hb : scanBlock x bs with
                | none =>
                    simp only [hb] at hd
                    rw [scanBlock_leak r (by simp [hb]) h,
                      ih rest _ _ hd hrest (scanBlock_none hb h)]
                | some b =>
                    simp only [hb] at hd
                    subst hd
                    rw [scanBlock_leak r (by simp [hb]) h, scanBlock_true hb h]

/-- **Leakage of the elimination at fixed frame parameters.** Under a regime in
    which `mov` is quiet, the gathered block of the body without its dead
    immediate moves has the leakage trace of the gathered block of the body, from
    every state. -/
theorem dropDeadCore_leak (p : Nat × Nat × Nat) (r : DoitRegime)
    (hmov : r.leaksOperands .mov = false) :
    ∀ (body : Lcmd) (ls ls' : List (List (JInstr 64))), gatherList p body = some ls →
      gatherList p (dropDeadCore p body) = some ls' →
      ∀ s, blockLeakCT r s ls'.flatten = blockLeakCT r s ls.flatten := by
  intro body
  induction body with
  | nil =>
      intro ls ls' h h' s
      simp only [dropDeadCore] at h'
      rw [h] at h'
      cases h'
      rfl
  | cons i is ih =>
      intro ls ls' h h' s
      -- keeping `i` in front of the eliminated tail
      have keep : gatherList p (i :: dropDeadCore p is) = some ls' →
          blockLeakCT r s ls'.flatten = blockLeakCT r s ls.flatten := by
        intro hk
        rw [gatherList_cons] at h hk
        by_cases hr : isLret i = true
        · rw [ite_eq_left hr] at h hk
          exact ih ls ls' h hk s
        · rw [ite_eq_right hr] at h hk
          cases hi : lowerPrinted p.1 p.2.1 p.2.2 i.li_i with
          | none => simp [hi] at h
          | some js =>
              cases hrest : gatherList p is with
              | none => simp [hi, hrest] at h
              | some rest =>
                  cases hrest' : gatherList p (dropDeadCore p is) with
                  | none => simp [hi, hrest'] at hk
                  | some rest' =>
                      simp only [hi, hrest, Option.bind_some, Option.map_some,
                        Option.some.injEq] at h
                      simp only [hi, hrest', Option.bind_some, Option.map_some,
                        Option.some.injEq] at hk
                      subst h hk
                      simp only [List.flatten_cons, blockLeakCT_append',
                        ih rest rest' hrest hrest' (runBlock s js)]
      cases hd : deadImmReg? p i with
      | none =>
          simp only [dropDeadCore, hd] at h'
          exact keep h'
      | some x =>
          by_cases hdead : deadAfter p x is = true
          · simp only [dropDeadCore, hd, hdead, ite_true] at h'
            obtain ⟨k, hk⟩ := deadImmReg?_spec hd
            rw [gatherList_cons] at h
            by_cases hr : isLret i = true
            · rw [ite_eq_left hr] at h
              exact ih ls ls' h h' s
            · rw [ite_eq_right hr, hk] at h
              cases hrest : gatherList p is with
              | none => simp [hrest] at h
              | some rest =>
                  simp only [hrest, Option.bind_some, Option.map_some,
                    Option.some.injEq] at h
                  subst h
                  obtain ⟨rest'', h1, h2⟩ := dropDeadCore_gather p is rest hrest
                  rw [h'] at h1
                  cases h1
                  rw [ih rest ls' hrest h' s, List.flatten_cons, List.singleton_append,
                    blockLeakCT_cons]
                  have hq : instrLeakCT r s (JInstr.mov x (.imm k)) = [] := by
                    simp [instrLeakCT, instrLeak, JInstr.mnem, hmov]
                  rw [hq, List.nil_append]
                  exact (deadAfter_leak p x r is rest _ _ hdead hrest
                    (AgreeOff.setReg_left (r := x) s _)).symm
          · simp only [dropDeadCore, hd, hdead, Bool.false_eq_true, ite_false] at h'
            exact keep h'

/-- **Leakage of the elimination.** If a body and its elimination both gather, the
    two blocks have the same leakage trace from every state, under a regime in
    which `mov` is quiet. -/
theorem gatherPrinted_dropDeadImmBody_leak {body : Lcmd} {g g' : List (JInstr 64)}
    (h : gatherPrinted body = some g) (h' : gatherPrinted (dropDeadImmBody body) = some g')
    (r : DoitRegime) (hmov : r.leaksOperands .mov = false) (s : JState 64) :
    blockLeakCT r s g' = blockLeakCT r s g := by
  unfold dropDeadImmBody at h'
  dsimp only at h'
  split at h'
  · rename_i hp
    rw [gatherPrinted_eq, Option.map_eq_some_iff] at h h'
    obtain ⟨ls, hls, rfl⟩ := h
    obtain ⟨ls', hls', rfl⟩ := h'
    rw [hp] at hls'
    exact dropDeadCore_leak (bodyParams body) r hmov body ls ls' hls hls' s
  · rw [h] at h'
    cases h'
    rfl

/-- `mov` is quiet under `DoitRegime.doitm`. -/
theorem doitm_mov_quiet : DoitRegime.doitm.leaksOperands .mov = false := rfl

/-! ## 4. Constant time is preserved -/

/-- **The fold preserves constant time.** If the gathered block of a body is
    constant time for the public registers `pub`, the fold gathers and its block
    is constant time for `pub`. -/
theorem constIndexFoldBody_machineCT {body : Lcmd} {g : List (JInstr 64)}
    (h : gatherPrinted body = some g) (r : DoitRegime) (pub : PubPred)
    (hct : MachineCT r pub g) :
    ∃ g', gatherPrinted (constIndexFoldBody body) = some g' ∧ MachineCT r pub g' := by
  obtain ⟨g', h', -⟩ := gatherPrinted_constIndexFoldBody h
  refine ⟨g', h', fun s₁ s₂ hag => ?_⟩
  simp only [gatherPrinted_constIndexFoldBody_leak h h' r]
  exact hct s₁ s₂ hag

/-- **The elimination preserves constant time** under a regime in which `mov` is
    quiet. -/
theorem dropDeadImmBody_machineCT {body : Lcmd} {g : List (JInstr 64)}
    (h : gatherPrinted body = some g) (r : DoitRegime)
    (hmov : r.leaksOperands .mov = false) (pub : PubPred) (hct : MachineCT r pub g) :
    ∃ g', gatherPrinted (dropDeadImmBody body) = some g' ∧ MachineCT r pub g' := by
  obtain ⟨g', h', -⟩ := gatherPrinted_dropDeadImmBody h
  refine ⟨g', h', fun s₁ s₂ hag => ?_⟩
  simp only [gatherPrinted_dropDeadImmBody_leak h h' r hmov]
  exact hct s₁ s₂ hag

/-- **The fold followed by the elimination preserves constant time**, and the
    result runs to the machine state of the input from every state. -/
theorem foldDrop_machineCT {body : Lcmd} {g : List (JInstr 64)}
    (h : gatherPrinted body = some g) (r : DoitRegime)
    (hmov : r.leaksOperands .mov = false) (pub : PubPred) (hct : MachineCT r pub g) :
    ∃ g', gatherPrinted (dropDeadImmBody (constIndexFoldBody body)) = some g'
      ∧ (∀ s, runBlock s g' = runBlock s g) ∧ MachineCT r pub g' := by
  obtain ⟨g', h', hrun⟩ := gatherPrinted_dropDeadImm_constIndexFold h
  obtain ⟨g1, h1, -⟩ := gatherPrinted_constIndexFoldBody h
  refine ⟨g', h', hrun, fun s₁ s₂ hag => ?_⟩
  simp only [gatherPrinted_dropDeadImmBody_leak h1 h' r hmov,
    gatherPrinted_constIndexFoldBody_leak h h1 r]
  exact hct s₁ s₂ hag

end CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFoldCT
