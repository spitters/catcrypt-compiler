/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvMachCT
public import CatCrypt.Crypto.SecureCompilation.VIR.IsaMachineLoop

@[expose] public section

set_option autoImplicit false

/-!
# The `mpn_and_n` loop at the RV64 machine

`rvAndLoopProg` is the decoded program of the `mpn_and_n` kernel as a loop over its limb
count: the index initialisation, the zero-trip guard, the body `RvIsa.rvAndCode`, the back
branch and the two `ret`. Both branches are the register loop guard `BNE ctr, zero, top` of
`RvIsa.rvData`; the branch to the end label of its zero-trip guard is the `ret` after the
guard. The index of a branch target is `LprogIsa.wordTarget` of its byte displacement, as in
`RvMach.rvAct`.

The run is an instance of `IsaMachine.reachesIn_loopNode`: for `n` limbs the machine reaches
a `ret` in `rvAndLoopFuel n = 2 + 13 * n` steps. The invariant `RvAndInv` carries the array
bases, the index, the count and the memory invariant `MachineMem64.LimbInv`.

## Main definitions

* `rvAndLoopProg`, `rvAndLoopFuel`, `rvAndLoopEnd`, `rvAndLoopLeak`: the program, its step
  count, its final state and its trace.
* `RvAndInv`, `RvAndLoopEntry`, `RvAndLoopPub`: the loop invariant, the entry condition and
  the public agreement.

## Main results

* `rvAndCode_run`, `RvAndInv.step`: the effect of one run of the body.
* `rv_and_loop_reaches`, `rv_and_loop`: the run of the loop, and the limb-wise conjunction in
  the output array of the final memory.
* `rvAndLoopLeak_zktMemData_congr`, `mpn_and_n_loop_rvMach_ct`: under `RvRegime.zktMemData`
  the trace of the loop is a function of the array bases and the count.
-/

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvMach

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvIsa
open CatCrypt.Crypto.SecureCompilation.MachineMem64
open CatCrypt.Crypto.SecureCompilation.CT

/-! ## The code of the loop -/

/-- The index initialisation of the `mpn_and_n` loop: `ADDI a4, zero, 0`. -/
def rvAndInit : RMInst64 := .addi "a4" "zero" 0

/-- **The decoded program of the `mpn_and_n` loop at RV64.** Index 0 clears the limb index
    `a4`; index 1 is the zero-trip guard `BNE a2, zero` to the loop head at index 3, and
    falls through to the `ret` at index 2 when the count `a2` is zero; indices 3 to 14 are
    the body `rvAndCode`; index 15 is the back branch `BNE a2, zero` to index 3; index 16 is
    `ret`. -/
def rvAndLoopProg : List RvInstr :=
  [.op rvAndInit, .op (.bne "a2" "zero" 8), .ret] ++ rvAndCode.flatten.map .op ++
    [.op (.bne "a2" "zero" (-48)), .ret]

/-- The number of steps of the `mpn_and_n` loop before its `ret`, for `n` limbs: the
    initialisation and the guard, and thirteen steps for each limb. -/
def rvAndLoopFuel (n : Nat) : Nat := 2 + n * (12 + 1)

/-- The state at the `ret` of the `mpn_and_n` loop for `n` limbs: `n` runs of the body on the
    state after the initialisation. -/
def rvAndLoopEnd (n : Nat) (b : RMState64) : RMState64 :=
  (fun s => runRMBlock64 s rvAndCode.flatten)^[n] (evalRMInst64 b rvAndInit)

/-- **The trace of the `mpn_and_n` loop** for `n` limbs under the regime `r`: the leakage of
    the initialisation, the outcome of the guard, and for each limb the leakage of the body
    and the outcome of the back branch. -/
def rvAndLoopLeak (r : RvRegime) (n : Nat) (b : RMState64) : List CTLeak :=
  (rvOpLeak r b rvAndInit ++ [.branch (decide (b.regs.get "a2" ≠ 0))]) ++
    IsaMachine.loopLeak (fun s => runRMBlock64 s rvAndCode.flatten)
      (fun s => (rvMach r).blockLeak s rvAndCode.flatten) n (evalRMInst64 b rvAndInit)

/-! ## One iteration -/

/-- **The effect of the `mpn_and_n` body**: the array bases are unchanged, the index `a4`
    advances by one, the count `a2` drops by one, and the conjunction of the two input limbs
    at the index is written to the output limb at the index. -/
theorem rvAndCode_run (b : RMState64) :
    (runRMBlock64 b rvAndCode.flatten).regs.get "a0" = b.regs.get "a0" ∧
    (runRMBlock64 b rvAndCode.flatten).regs.get "a1" = b.regs.get "a1" ∧
    (runRMBlock64 b rvAndCode.flatten).regs.get "a3" = b.regs.get "a3" ∧
    (runRMBlock64 b rvAndCode.flatten).regs.get "a4" = b.regs.get "a4" + 1 ∧
    (runRMBlock64 b rvAndCode.flatten).regs.get "a2" = b.regs.get "a2" - 1 ∧
    (runRMBlock64 b rvAndCode.flatten).mem =
      write64 b.mem (b.regs.get "a3" + (b.regs.get "a4" <<< 3))
        (read64 b.mem (b.regs.get "a1" + (b.regs.get "a4" <<< 3)) &&&
          read64 b.mem (b.regs.get "a0" + (b.regs.get "a4" <<< 3))) := by
  simp [rvAndCode, rvIdxAddr, evalRMInst64, evalRInst64, RState64.set, rvAddr]
  bv_omega

/-- **The invariant of the `mpn_and_n` loop** with `j` iterations remaining, for `n` limbs,
    the inputs `A` at `pa` and `B` at `pb` and the output at `po`: the bases are in `a1`,
    `a0`, `a3`, the index `a4` is `n - j`, the count `a2` is `j`, and the memory satisfies
    `LimbInv` at `n - j`. -/
def RvAndInv (n : Nat) (pa pb po : BitVec 64) (A B : Fin n → BitVec 64) (j : Nat)
    (b : RMState64) : Prop :=
  j ≤ n ∧ b.regs.get "a1" = pa ∧ b.regs.get "a0" = pb ∧ b.regs.get "a3" = po ∧
    b.regs.get "a4" = BitVec.ofNat 64 (n - j) ∧ b.regs.get "a2" = BitVec.ofNat 64 j ∧
    LimbInv (fun x y => x &&& y) n pa pb po A B (n - j) b.mem

/-- **One run of the body takes the invariant from `j + 1` remaining iterations to `j`.** -/
theorem RvAndInv.step {n : Nat} {pa pb po : BitVec 64} {A B : Fin n → BitVec 64} {j : Nat}
    {b : RMState64} (h : RvAndInv n pa pb po A B (j + 1) b) (hn : 8 * n ≤ 2 ^ 64)
    (hsa : ∀ j k : Fin n,
      MemSep (po + BitVec.ofNat 64 (8 * j.val)) (pa + BitVec.ofNat 64 (8 * k.val)))
    (hsb : ∀ j k : Fin n,
      MemSep (po + BitVec.ofNat 64 (8 * j.val)) (pb + BitVec.ofNat 64 (8 * k.val))) :
    RvAndInv n pa pb po A B j (runRMBlock64 b rvAndCode.flatten) := by
  obtain ⟨hj, h1, h0, h3, h4, h2, hm⟩ := h
  obtain ⟨e0, e1, e3, e4, e2, em⟩ := rvAndCode_run b
  have hi : n - (j + 1) < n := by omega
  have hsh : b.regs.get "a4" <<< 3 = BitVec.ofNat 64 (8 * (n - (j + 1))) := by
    rw [shl3_eq, h4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨by omega, e1.trans h1, e0.trans h0, e3.trans h3, ?_, ?_, ?_⟩
  · rw [e4, h4, show n - j = n - (j + 1) + 1 by omega]
    simp [BitVec.ofNat_add]
  · rw [e2, h2]
    simp [BitVec.ofNat_add]
  · rw [em, hsh, h1, h0, h3, show n - j = n - (j + 1) + 1 by omega]
    exact hm.step hi hn hsa hsb

/-! ## The loop -/

/-- **The entry condition of the `mpn_and_n` loop** for `n` limbs: the arrays at `a0`, `a1`,
    `a3` are laid out separately and the count `a2` is `n`. -/
def RvAndLoopEntry (n : Nat) (b : RMState64) : Prop :=
  RvArrsSep rvAndArrs (fun _ => n) b.regs.get ∧ b.regs.get "a2" = BitVec.ofNat 64 n

variable (r : RvRegime)

/-- **The `mpn_and_n` loop at `rvMach`, as a path.** From a state that satisfies
    `RvAndLoopEntry n`, with the inputs `A` at `a1` and `B` at `a0`, the machine reaches a
    `ret` (index 2 at `n = 0`, index 16 otherwise) in `rvAndLoopFuel n` steps, in the state
    `rvAndLoopEnd n b`, with the trace `rvAndLoopLeak r n b`; the invariant holds there with
    no iteration remaining. -/
theorem rv_and_loop_reaches (n : Nat) (A B : Fin n → BitVec 64) (b : RMState64)
    (hentry : RvAndLoopEntry n b) (ha : ArrAt b.mem (b.regs.get "a1") n A)
    (hb : ArrAt b.mem (b.regs.get "a0") n B) :
    (rvMach r).ReachesIn rvAndLoopProg (rvAndLoopFuel n) 0 b (rvAndLoopLeak r n b)
        (if n = 0 then 2 else 16) (rvAndLoopEnd n b) ∧
      RvAndInv n (b.regs.get "a1") (b.regs.get "a0") (b.regs.get "a3") A B 0
        (rvAndLoopEnd n b) := by
  obtain ⟨⟨-, hsz, hss⟩, hcnt⟩ := hentry
  have hn : 8 * n ≤ 2 ^ 64 := hsz "a3" (by simp [rvAndArrs])
  have hsa := hss "a3" (by simp [rvAndArrs]) "a1" (by simp [rvAndArrs]) (by decide)
  have hsb := hss "a3" (by simp [rvAndArrs]) "a0" (by simp [rvAndArrs]) (by decide)
  refine IsaMachine.reachesIn_loopNode (M := rvMach r) (prog := rvAndLoopProg) (g := 0)
    (top := 3) (foot := 15) (exit₀ := 2) (ng := 2) (nb := 12)
    (G := fun s => evalRMInst64 s rvAndInit) (F := fun s => runRMBlock64 s rvAndCode.flatten)
    (Tg := fun s => rvOpLeak r s rvAndInit ++ [.branch (decide (s.regs.get "a2" ≠ 0))])
    (T := fun s => (rvMach r).blockLeak s rvAndCode.flatten)
    (Pre := fun k s => k = n ∧ s = b)
    (Inv := RvAndInv n (b.regs.get "a1") (b.regs.get "a0") (b.regs.get "a3") A B)
    ?_ ?_ ?_ ?_ ?_ n b ⟨rfl, rfl⟩
  · rintro k s ⟨rfl, rfl⟩
    have h0 : (rvMach r).mstep rvAndLoopProg 0 s = some (.go 1 (evalRMInst64 s rvAndInit)) := by
      simp [IsaMachine.mstep, rvAct, rvAndLoopProg, rvAndInit]
    have h1 : (rvMach r).act rvAndLoopProg 1 (evalRMInst64 s rvAndInit)
        = some (.branch (decide (s.regs.get "a2" ≠ 0)) 3) := by
      simp [rvAct, rvAndLoopProg, wordTarget, rvAndInit, evalRMInst64, RState64.set]
    refine (IsaMachine.ReachesIn.next h0 (IsaMachine.reachesIn_branch h1)).congr rfl ?_ ?_ rfl
    · simp [IsaMachine.stepLeak, rvAct, rvAndLoopProg, rvAndInit]
    · rw [hcnt, decide_ofNat64_ne_zero (by omega)]
      by_cases hk : k = 0 <;> simp [hk]
  · rintro k s ⟨rfl, rfl⟩
    refine ⟨Nat.le_refl _, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [rvAndInit, evalRMInst64, RState64.set]
    · simp [rvAndInit, evalRMInst64, RState64.set]
    · simp [rvAndInit, evalRMInst64, RState64.set]
    · simp [rvAndInit, evalRMInst64, RState64.set]
    · rw [← hcnt]
      simp [rvAndInit, evalRMInst64, RState64.set]
    · rw [Nat.sub_self]
      exact ⟨ha, hb, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  · intro j s _
    have h := IsaMachine.reachesIn_ops (M := rvMach r) rvAndCode.flatten 3 s
      (rvMach_opsAt r [.op rvAndInit, .op (.bne "a2" "zero" 8), .ret] rvAndCode.flatten
        [.op (.bne "a2" "zero" (-48)), .ret] rvAndCode_straight)
    rw [rvMach_runBlock] at h
    exact h
  · intro j s hI
    obtain ⟨hj, -, -, -, -, h2, -⟩ := hI.step hn hsa hsb
    have : (rvMach r).act rvAndLoopProg 15 (runRMBlock64 s rvAndCode.flatten)
        = some (.branch (decide ((runRMBlock64 s rvAndCode.flatten).regs.get "a2" ≠ 0)) 3) := by
      simp [rvAct, rvAndLoopProg, rvAndCode, rvIdxAddr, wordTarget]
    rw [this, h2, decide_ofNat64_ne_zero (by omega)]
  · intro j s hI
    exact hI.step hn hsa hsb

/-- **The `mpn_and_n` loop at `rvMach`: value.** From a state that satisfies
    `RvAndLoopEntry n`, with the inputs `A` at `a1` and `B` at `a0`, the decoded program
    reaches its `ret` in `rvAndLoopFuel n` steps and halts there with the trace
    `rvAndLoopLeak r n b`; in the final memory the output array at `a3` holds the limb-wise
    conjunction of `A` and `B`, and the inputs are in place. -/
theorem rv_and_loop (n : Nat) (A B : Fin n → BitVec 64) (b : RMState64)
    (hentry : RvAndLoopEntry n b) (ha : ArrAt b.mem (b.regs.get "a1") n A)
    (hb : ArrAt b.mem (b.regs.get "a0") n B) :
    ∃ b', (rvMach r).ReachesIn rvAndLoopProg (rvAndLoopFuel n) 0 b (rvAndLoopLeak r n b)
        (if n = 0 then 2 else 16) b'
      ∧ (rvMach r).Halts rvAndLoopProg 0 b b'
      ∧ (rvMach r).RunL (fun _ _ => True) rvAndLoopProg 0 b (rvAndLoopLeak r n b) b'
      ∧ ArrAt b'.mem (b.regs.get "a3") n (fun k => A k &&& B k)
      ∧ ArrAt b'.mem (b.regs.get "a1") n A ∧ ArrAt b'.mem (b.regs.get "a0") n B := by
  obtain ⟨hr, -, -, -, -, -, -, hA, hB, hO⟩ := rv_and_loop_reaches r n A B b hentry ha hb
  have hret : (rvMach r).act rvAndLoopProg (if n = 0 then 2 else 16) (rvAndLoopEnd n b)
      = some .ret := by
    split
    · exact rvAct_ret (prog := rvAndLoopProg) (pc := 2) rfl (rvAndLoopEnd n b)
    · exact rvAct_ret (prog := rvAndLoopProg) (pc := 16) rfl (rvAndLoopEnd n b)
  refine ⟨_, hr, ⟨_, hr.reaches, hret⟩, ?_, fun k => hO k (by omega), hA, hB⟩
  simpa using hr.runL (.ret hret)

/-! ## Constant time of the loop under `RvRegime.zktMemData` -/

/-- **The public agreement of two machine states** for the `mpn_and_n` loop: equal array
    bases `a0`, `a1`, `a3` and equal count `a2`. -/
def RvAndLoopPub (b₁ b₂ : RMState64) : Prop :=
  b₁.regs.get "a0" = b₂.regs.get "a0" ∧ b₁.regs.get "a1" = b₂.regs.get "a1" ∧
    b₁.regs.get "a2" = b₂.regs.get "a2" ∧ b₁.regs.get "a3" = b₂.regs.get "a3"

/-- The body takes states that agree on the bases and the index to states that agree on
    them. -/
theorem rvAndCode_pub {b₁ b₂ : RMState64} (h : RvAndPub b₁ b₂) :
    RvAndPub (runRMBlock64 b₁ rvAndCode.flatten) (runRMBlock64 b₂ rvAndCode.flatten) := by
  obtain ⟨h0, h1, h3, h4⟩ := h
  obtain ⟨a0, a1, a3, a4, -, -⟩ := rvAndCode_run b₁
  obtain ⟨c0, c1, c3, c4, -, -⟩ := rvAndCode_run b₂
  exact ⟨by rw [a0, c0, h0], by rw [a1, c1, h1], by rw [a3, c3, h3], by rw [a4, c4, h4]⟩

/-- **The trace of the loop under `RvRegime.zktMemData` is a function of the public data**:
    states that agree on the array bases and the count have the same `rvAndLoopLeak`. -/
theorem rvAndLoopLeak_zktMemData_congr (n : Nat) {b₁ b₂ : RMState64}
    (h : RvAndLoopPub b₁ b₂) :
    rvAndLoopLeak .zktMemData n b₁ = rvAndLoopLeak .zktMemData n b₂ := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  unfold rvAndLoopLeak
  congr 1
  · rw [rvOpLeak_zktMemData, rvOpLeak_zktMemData, h2]
    simp [rmAddrLeak, rmAddr?, rvAndInit]
  · refine IsaMachine.loopLeak_congr (R := RvAndPub) ?_ (fun _ _ => rvAndCode_pub) n _ _ ?_
    · intro s₁ s₂ hp
      rw [rvAndCode_leak_zktMemData, rvAndCode_leak_zktMemData]
      exact rvAndTrace_congr hp
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [rvAndInit, evalRMInst64, RState64.set] using h0
      · simpa [rvAndInit, evalRMInst64, RState64.set] using h1
      · simpa [rvAndInit, evalRMInst64, RState64.set] using h3
      · simp [rvAndInit, evalRMInst64, RState64.set]

/-- **The `mpn_and_n` loop is constant time at the RV64 machine under
    `RvRegime.zktMemData`.** Two halting runs of `rvAndLoopProg` from index 0, from states
    that agree on the array bases `a0`, `a1`, `a3` and on the count `a2`, the first
    satisfying `RvAndLoopEntry n`, have equal leakage traces. The trace holds the three
    addresses of each limb access and the outcomes of the guard and of the back branch.

    The statement holds under the regime constructor `RvRegime.zktMemData`, as stated at
    `mpn_and_n_rvMach_ct`. -/
theorem mpn_and_n_loop_rvMach_ct (n : Nat) :
    ConstantTimeRel (fun b₁ b₂ => RvAndLoopPub b₁ b₂ ∧ RvAndLoopEntry n b₁)
      (fun b t => ∃ b', (rvMach .zktMemData).RunL (fun _ _ => True) rvAndLoopProg 0 b t b') := by
  rintro b₁ b₂ t₁ t₂ ⟨hp, he⟩ ⟨s₁, h₁⟩ ⟨s₂, h₂⟩
  have he₂ : RvAndLoopEntry n b₂ := by
    obtain ⟨h0, h1, h2, h3⟩ := hp
    refine ⟨RvArrsSep_congr he.1 ?_, h2 ▸ he.2⟩
    intro a ha
    simp only [rvAndArrs, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact h0.symm
    · exact h1.symm
    · exact h3.symm
  obtain ⟨_, -, -, hl₁, -⟩ := rv_and_loop .zktMemData n _ _ b₁ he (fun _ => rfl) (fun _ => rfl)
  obtain ⟨_, -, -, hl₂, -⟩ := rv_and_loop .zktMemData n _ _ b₂ he₂ (fun _ => rfl) (fun _ => rfl)
  rw [(runL_det h₁ hl₁).1, (runL_det h₂ hl₂).1]
  exact rvAndLoopLeak_zktMemData_congr n hp

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvMach
