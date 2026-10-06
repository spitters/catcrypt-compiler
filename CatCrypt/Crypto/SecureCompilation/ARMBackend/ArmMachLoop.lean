/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmMachCT
public import CatCrypt.Crypto.SecureCompilation.VIR.IsaMachineLoop

@[expose] public section

set_option autoImplicit false

/-!
# The `mpn_and_n` loop at the AArch64 machine

`armAndLoopProg` is the decoded program of the `mpn_and_n` kernel as a loop over its limb
count: the index initialisation, the zero-trip guard, the body `ArmIsa.armAndCode`, the back
branch and the two `RET`. Both branches are the register loop guard `CBNZ ctr, top` of
`ArmIsa.armData`. The index of a branch target is `LprogIsa.wordTarget` of its byte
displacement, as in `ArmMach.armAct`.

The run is an instance of `IsaMachine.reachesIn_loopNode`: for `n` limbs the machine reaches
a `RET` in `armAndLoopFuel n = 2 + 7 * n` steps. The invariant `ArmAndInv` carries the array
bases, the index, the count and the memory invariant `MachineMem64.LimbInv`.

## Main definitions

* `armAndLoopProg`, `armAndLoopFuel`, `armAndLoopEnd`, `armAndLoopLeak`: the program, its
  step count, its final state and its trace.
* `ArmAndInv`, `ArmAndLoopEntry`, `ArmAndLoopPub`: the loop invariant, the entry condition
  and the public agreement.

## Main results

* `armAndCode_run`, `ArmAndInv.step`: the effect of one run of the body.
* `arm_and_loop_reaches`, `arm_and_loop`: the run of the loop, and the limb-wise conjunction
  in the output array of the final memory.
* `armAndLoopLeak_dit_congr`, `mpn_and_n_loop_armMach_ct`: under `ArmRegime.dit` the trace of
  the loop is a function of the array bases and the count.
-/

namespace CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmMach

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
open CatCrypt.Crypto.SecureCompilation.ARMBackend
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmIsa
open CatCrypt.Crypto.SecureCompilation.MachineMem64
open CatCrypt.Crypto.SecureCompilation.CT

/-! ## The code of the loop -/

/-- The index initialisation of the `mpn_and_n` loop: `EOR x4, x4, x4`. -/
def armAndInit : BMInst := .alu (.eor "x4" "x4" "x4")

/-- **The decoded program of the `mpn_and_n` loop at AArch64.** Index 0 clears the limb index
    `x4`; index 1 is the zero-trip guard `CBNZ x2` to the loop head at index 3, and falls
    through to the `RET` at index 2 when the count `x2` is zero; indices 3 to 8 are the body
    `armAndCode`; index 9 is the back branch `CBNZ x2` to index 3; index 10 is `RET`. -/
def armAndLoopProg : List ArmInstr :=
  [.op armAndInit, .op (.cbnz "x2" 8), .ret] ++ armAndCode.map .op ++
    [.op (.cbnz "x2" (-24)), .ret]

/-- The number of steps of the `mpn_and_n` loop before its `RET`, for `n` limbs: the
    initialisation and the guard, and seven steps for each limb. -/
def armAndLoopFuel (n : Nat) : Nat := 2 + n * (6 + 1)

/-- The state at the `RET` of the `mpn_and_n` loop for `n` limbs: `n` runs of the body on the
    state after the initialisation. -/
def armAndLoopEnd (n : Nat) (b : BMState) : BMState :=
  (fun s => runBMBlock s armAndCode)^[n] (evalBMInst b armAndInit)

/-- **The trace of the `mpn_and_n` loop** for `n` limbs under the regime `r`: the leakage of
    the initialisation, the outcome of the guard, and for each limb the leakage of the body
    and the outcome of the back branch. -/
def armAndLoopLeak (r : ArmRegime) (n : Nat) (b : BMState) : List CTLeak :=
  (armOpLeak r b armAndInit ++ [.branch (decide (b.regs.get "x2" ≠ 0))]) ++
    IsaMachine.loopLeak (fun s => runBMBlock s armAndCode)
      (fun s => (armMach r).blockLeak s armAndCode) n (evalBMInst b armAndInit)

/-! ## One iteration -/

/-- **The effect of the `mpn_and_n` body**: the array bases are unchanged, the index `x4`
    advances by one, the count `x2` drops by one, and the conjunction of the two input limbs
    at the index is written to the output limb at the index. -/
theorem armAndCode_run (b : BMState) :
    (runBMBlock b armAndCode).regs.get "x0" = b.regs.get "x0" ∧
    (runBMBlock b armAndCode).regs.get "x1" = b.regs.get "x1" ∧
    (runBMBlock b armAndCode).regs.get "x3" = b.regs.get "x3" ∧
    (runBMBlock b armAndCode).regs.get "x4" = b.regs.get "x4" + 1 ∧
    (runBMBlock b armAndCode).regs.get "x2" = b.regs.get "x2" - 1 ∧
    (runBMBlock b armAndCode).mem = write64 b.mem (b.regs.get "x3" + (b.regs.get "x4" <<< 3))
      (opAnd64 (read64 b.mem (b.regs.get "x1" + (b.regs.get "x4" <<< 3)))
        (read64 b.mem (b.regs.get "x0" + (b.regs.get "x4" <<< 3)))) := by
  simp [armAndCode, evalBMInst, evalBInst, BState.set, armAddrR]

/-- **The invariant of the `mpn_and_n` loop** with `j` iterations remaining, for `n` limbs,
    the inputs `A` at `pa` and `B` at `pb` and the output at `po`: the bases are in `x1`,
    `x0`, `x3`, the index `x4` is `n - j`, the count `x2` is `j`, and the memory satisfies
    `LimbInv` at `n - j`. -/
def ArmAndInv (n : Nat) (pa pb po : BitVec 64) (A B : Fin n → BitVec 64) (j : Nat)
    (b : BMState) : Prop :=
  j ≤ n ∧ b.regs.get "x1" = pa ∧ b.regs.get "x0" = pb ∧ b.regs.get "x3" = po ∧
    b.regs.get "x4" = BitVec.ofNat 64 (n - j) ∧ b.regs.get "x2" = BitVec.ofNat 64 j ∧
    LimbInv opAnd64 n pa pb po A B (n - j) b.mem

/-- **One run of the body takes the invariant from `j + 1` remaining iterations to `j`.** -/
theorem ArmAndInv.step {n : Nat} {pa pb po : BitVec 64} {A B : Fin n → BitVec 64} {j : Nat}
    {b : BMState} (h : ArmAndInv n pa pb po A B (j + 1) b) (hn : 8 * n ≤ 2 ^ 64)
    (hsa : ∀ j k : Fin n,
      MemSep (po + BitVec.ofNat 64 (8 * j.val)) (pa + BitVec.ofNat 64 (8 * k.val)))
    (hsb : ∀ j k : Fin n,
      MemSep (po + BitVec.ofNat 64 (8 * j.val)) (pb + BitVec.ofNat 64 (8 * k.val))) :
    ArmAndInv n pa pb po A B j (runBMBlock b armAndCode) := by
  obtain ⟨hj, h1, h0, h3, h4, h2, hm⟩ := h
  obtain ⟨e0, e1, e3, e4, e2, em⟩ := armAndCode_run b
  have hi : n - (j + 1) < n := by omega
  have hsh : b.regs.get "x4" <<< 3 = BitVec.ofNat 64 (8 * (n - (j + 1))) := by
    rw [shiftLeft_three_eq, h4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨by omega, e1.trans h1, e0.trans h0, e3.trans h3, ?_, ?_, ?_⟩
  · rw [e4, h4, show n - j = n - (j + 1) + 1 by omega]
    simp [BitVec.ofNat_add]
  · rw [e2, h2]
    simp [BitVec.ofNat_add]
  · rw [em, hsh, h1, h0, h3, show n - j = n - (j + 1) + 1 by omega]
    exact hm.step hi hn hsa hsb

/-! ## The loop -/

/-- **The entry condition of the `mpn_and_n` loop** for `n` limbs: the arrays at `x0`, `x1`,
    `x3` are laid out separately and the count `x2` is `n`. -/
def ArmAndLoopEntry (n : Nat) (b : BMState) : Prop :=
  ArmArrsSep armAndArrs (fun _ => n) b.regs.get ∧ b.regs.get "x2" = BitVec.ofNat 64 n

variable (r : ArmRegime)

/-- **The `mpn_and_n` loop at `armMach`, as a path.** From a state that satisfies
    `ArmAndLoopEntry n`, with the inputs `A` at `x1` and `B` at `x0`, the machine reaches a
    `RET` (index 2 at `n = 0`, index 10 otherwise) in `armAndLoopFuel n` steps, in the state
    `armAndLoopEnd n b`, with the trace `armAndLoopLeak r n b`; the invariant holds there with
    no iteration remaining. -/
theorem arm_and_loop_reaches (n : Nat) (A B : Fin n → BitVec 64) (b : BMState)
    (hentry : ArmAndLoopEntry n b) (ha : ArrAt b.mem (b.regs.get "x1") n A)
    (hb : ArrAt b.mem (b.regs.get "x0") n B) :
    (armMach r).ReachesIn armAndLoopProg (armAndLoopFuel n) 0 b (armAndLoopLeak r n b)
        (if n = 0 then 2 else 10) (armAndLoopEnd n b) ∧
      ArmAndInv n (b.regs.get "x1") (b.regs.get "x0") (b.regs.get "x3") A B 0
        (armAndLoopEnd n b) := by
  obtain ⟨⟨-, hsz, hss⟩, hcnt⟩ := hentry
  have hn : 8 * n ≤ 2 ^ 64 := hsz "x3" (by simp [armAndArrs])
  have hsa := hss "x3" (by simp [armAndArrs]) "x1" (by simp [armAndArrs]) (by decide)
  have hsb := hss "x3" (by simp [armAndArrs]) "x0" (by simp [armAndArrs]) (by decide)
  refine IsaMachine.reachesIn_loopNode (M := armMach r) (prog := armAndLoopProg) (g := 0)
    (top := 3) (foot := 9) (exit₀ := 2) (ng := 2) (nb := 6)
    (G := fun s => evalBMInst s armAndInit) (F := fun s => runBMBlock s armAndCode)
    (Tg := fun s => armOpLeak r s armAndInit ++ [.branch (decide (s.regs.get "x2" ≠ 0))])
    (T := fun s => (armMach r).blockLeak s armAndCode)
    (Pre := fun k s => k = n ∧ s = b)
    (Inv := ArmAndInv n (b.regs.get "x1") (b.regs.get "x0") (b.regs.get "x3") A B)
    ?_ ?_ ?_ ?_ ?_ n b ⟨rfl, rfl⟩
  · rintro k s ⟨rfl, rfl⟩
    have h0 : (armMach r).mstep armAndLoopProg 0 s = some (.go 1 (evalBMInst s armAndInit)) := by
      simp [IsaMachine.mstep, armAct, armAndLoopProg, armAndInit]
    have h1 : (armMach r).act armAndLoopProg 1 (evalBMInst s armAndInit)
        = some (.branch (decide (s.regs.get "x2" ≠ 0)) 3) := by
      simp [armAct, armAndLoopProg, wordTarget, armAndInit, evalBMInst, evalBInst, BState.set]
    refine (IsaMachine.ReachesIn.next h0 (IsaMachine.reachesIn_branch h1)).congr rfl ?_ ?_ rfl
    · simp [IsaMachine.stepLeak, armAct, armAndLoopProg, armAndInit]
    · rw [hcnt, decide_ofNat64_ne_zero (by omega)]
      by_cases hk : k = 0 <;> simp [hk]
  · rintro k s ⟨rfl, rfl⟩
    refine ⟨Nat.le_refl _, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [armAndInit, evalBMInst, evalBInst, BState.set]
    · simp [armAndInit, evalBMInst, evalBInst, BState.set]
    · simp [armAndInit, evalBMInst, evalBInst, BState.set]
    · simp [armAndInit, evalBMInst, evalBInst, BState.set, opEor64]
    · rw [← hcnt]
      simp [armAndInit, evalBMInst, evalBInst, BState.set]
    · rw [Nat.sub_self]
      exact ⟨ha, hb, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  · intro j s _
    have h := IsaMachine.reachesIn_ops (M := armMach r) armAndCode 3 s
      (armMach_opsAt r [.op armAndInit, .op (.cbnz "x2" 8), .ret] armAndCode
        [.op (.cbnz "x2" (-24)), .ret] armAndCode_straight)
    rw [armMach_runBlock] at h
    exact h
  · intro j s hI
    obtain ⟨hj, -, -, -, -, h2, -⟩ := hI.step hn hsa hsb
    have : (armMach r).act armAndLoopProg 9 (runBMBlock s armAndCode)
        = some (.branch (decide ((runBMBlock s armAndCode).regs.get "x2" ≠ 0)) 3) := by
      simp [armAct, armAndLoopProg, armAndCode, wordTarget]
    rw [this, h2, decide_ofNat64_ne_zero (by omega)]
  · intro j s hI
    exact hI.step hn hsa hsb

/-- **The `mpn_and_n` loop at `armMach`: value.** From a state that satisfies
    `ArmAndLoopEntry n`, with the inputs `A` at `x1` and `B` at `x0`, the decoded program
    reaches its `RET` in `armAndLoopFuel n` steps and halts there with the trace
    `armAndLoopLeak r n b`; in the final memory the output array at `x3` holds the limb-wise
    conjunction of `A` and `B`, and the inputs are in place. -/
theorem arm_and_loop (n : Nat) (A B : Fin n → BitVec 64) (b : BMState)
    (hentry : ArmAndLoopEntry n b) (ha : ArrAt b.mem (b.regs.get "x1") n A)
    (hb : ArrAt b.mem (b.regs.get "x0") n B) :
    ∃ b', (armMach r).ReachesIn armAndLoopProg (armAndLoopFuel n) 0 b (armAndLoopLeak r n b)
        (if n = 0 then 2 else 10) b'
      ∧ (armMach r).Halts armAndLoopProg 0 b b'
      ∧ (armMach r).RunL (fun _ _ => True) armAndLoopProg 0 b (armAndLoopLeak r n b) b'
      ∧ ArrAt b'.mem (b.regs.get "x3") n (fun k => opAnd64 (A k) (B k))
      ∧ ArrAt b'.mem (b.regs.get "x1") n A ∧ ArrAt b'.mem (b.regs.get "x0") n B := by
  obtain ⟨hr, -, -, -, -, -, -, hA, hB, hO⟩ := arm_and_loop_reaches r n A B b hentry ha hb
  have hret : (armMach r).act armAndLoopProg (if n = 0 then 2 else 10) (armAndLoopEnd n b)
      = some .ret := by
    split
    · exact armAct_ret (prog := armAndLoopProg) (pc := 2) rfl (armAndLoopEnd n b)
    · exact armAct_ret (prog := armAndLoopProg) (pc := 10) rfl (armAndLoopEnd n b)
  refine ⟨_, hr, ⟨_, hr.reaches, hret⟩, ?_, fun k => hO k (by omega), hA, hB⟩
  simpa using hr.runL (.ret hret)

/-! ## Constant time of the loop under `PSTATE.DIT = 1` -/

/-- **The public agreement of two machine states** for the `mpn_and_n` loop: equal array
    bases `x0`, `x1`, `x3` and equal count `x2`. -/
def ArmAndLoopPub (b₁ b₂ : BMState) : Prop :=
  b₁.regs.get "x0" = b₂.regs.get "x0" ∧ b₁.regs.get "x1" = b₂.regs.get "x1" ∧
    b₁.regs.get "x2" = b₂.regs.get "x2" ∧ b₁.regs.get "x3" = b₂.regs.get "x3"

/-- The body takes states that agree on the bases and the index to states that agree on
    them. -/
theorem armAndCode_pub {b₁ b₂ : BMState} (h : ArmAndPub b₁ b₂) :
    ArmAndPub (runBMBlock b₁ armAndCode) (runBMBlock b₂ armAndCode) := by
  obtain ⟨h0, h1, h3, h4⟩ := h
  obtain ⟨a0, a1, a3, a4, -, -⟩ := armAndCode_run b₁
  obtain ⟨c0, c1, c3, c4, -, -⟩ := armAndCode_run b₂
  exact ⟨by rw [a0, c0, h0], by rw [a1, c1, h1], by rw [a3, c3, h3], by rw [a4, c4, h4]⟩

/-- **The trace of the loop under `PSTATE.DIT = 1` is a function of the public data**: states
    that agree on the array bases and the count have the same `armAndLoopLeak`. -/
theorem armAndLoopLeak_dit_congr (n : Nat) {b₁ b₂ : BMState} (h : ArmAndLoopPub b₁ b₂) :
    armAndLoopLeak .dit n b₁ = armAndLoopLeak .dit n b₂ := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  unfold armAndLoopLeak
  congr 1
  · rw [armOpLeak_dit, armOpLeak_dit, h2]
    simp [bmAddrLeak, bmAddr?, armAndInit]
  · refine IsaMachine.loopLeak_congr (R := ArmAndPub) ?_ (fun _ _ => armAndCode_pub) n _ _ ?_
    · intro s₁ s₂ hp
      rw [armAndCode_leak_dit, armAndCode_leak_dit]
      exact armAndTrace_congr hp
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [armAndInit, evalBMInst, evalBInst, BState.set] using h0
      · simpa [armAndInit, evalBMInst, evalBInst, BState.set] using h1
      · simpa [armAndInit, evalBMInst, evalBInst, BState.set] using h3
      · simp [armAndInit, evalBMInst, evalBInst, BState.set, opEor64]

/-- **The `mpn_and_n` loop is constant time at the AArch64 machine under `PSTATE.DIT = 1`.**
    Two halting runs of `armAndLoopProg` from index 0, from states that agree on the array
    bases `x0`, `x1`, `x3` and on the count `x2`, the first satisfying `ArmAndLoopEntry n`,
    have equal leakage traces. The trace holds the three addresses of each limb access and
    the outcomes of the guard and of the back branch.

    The statement holds under the regime constructor `ArmRegime.dit`, as stated at
    `mpn_and_n_armMach_ct`. -/
theorem mpn_and_n_loop_armMach_ct (n : Nat) :
    ConstantTimeRel (fun b₁ b₂ => ArmAndLoopPub b₁ b₂ ∧ ArmAndLoopEntry n b₁)
      (fun b t => ∃ b', (armMach .dit).RunL (fun _ _ => True) armAndLoopProg 0 b t b') := by
  rintro b₁ b₂ t₁ t₂ ⟨hp, he⟩ ⟨s₁, h₁⟩ ⟨s₂, h₂⟩
  have he₂ : ArmAndLoopEntry n b₂ := by
    obtain ⟨h0, h1, h2, h3⟩ := hp
    refine ⟨ArmArrsSep_congr he.1 ?_, h2 ▸ he.2⟩
    intro a ha
    simp only [armAndArrs, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact h0.symm
    · exact h1.symm
    · exact h3.symm
  obtain ⟨_, -, -, hl₁, -⟩ := arm_and_loop .dit n _ _ b₁ he (fun _ => rfl) (fun _ => rfl)
  obtain ⟨_, -, -, hl₂, -⟩ := arm_and_loop .dit n _ _ b₂ he₂ (fun _ => rfl) (fun _ => rfl)
  rw [(runL_det h₁ hl₁).1, (runL_det h₂ hl₂).1]
  exact armAndLoopLeak_dit_congr n hp

end CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmMach
