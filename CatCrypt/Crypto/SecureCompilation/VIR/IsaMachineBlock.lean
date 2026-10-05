/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.IsaMachine

@[expose] public section

set_option autoImplicit false

/-!
# Straight-line segments of a decoded program over `IsaMachine`

A segment of a decoded program is straight-line at an index `pc` for a list of operations
`ops` when the action at `pc + k` is the operation `ops[k]` in every state (`OpsAt`). Over
such a segment the machine reaches the index after it in the state `runBlock s ops`, and when
the action after the segment is `ret` the program halts there with the leakage
`blockLeak s ops`. These are the `IsaMachine` forms of `RInstrSemantics.reaches_ops`.

`wordTarget` is the index a relative branch of a fixed-width instruction set reaches: the
branch at index `pc` with the signed byte displacement `off` over 4-byte words.

## Main definitions

* `IsaMachine.OpsAt`: the actions of a segment are the operations of a list.
* `wordTarget`: the target index of a relative branch over 4-byte words.

## Main results

* `IsaMachine.reaches_ops`: the machine reaches the end of a straight-line segment.
* `IsaMachine.halts_ops`, `IsaMachine.runL_ops`: a straight-line segment followed by `ret`
  halts, with the leakage of the block.
* `wordTarget_ofNat`: the byte address of the target is the byte address of the branch plus
  the displacement.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa

open CatCrypt.Crypto.SecureCompilation.CT

namespace IsaMachine

variable {M : IsaMachine}

/-- The actions of `prog` at the indices `pc, …, pc + ops.length - 1` are the operations of
    `ops`, in every state. -/
def OpsAt (M : IsaMachine) (prog : List M.Instr) (pc : Nat) (ops : List M.Op) : Prop :=
  ∀ (k : Nat) (h : k < ops.length) (s : M.MState), M.act prog (pc + k) s = some (.op ops[k])

/-- The tail of a straight-line segment is a straight-line segment at the next index. -/
theorem OpsAt.tail {prog : List M.Instr} {pc : Nat} {i : M.Op} {is : List M.Op}
    (h : M.OpsAt prog pc (i :: is)) : M.OpsAt prog (pc + 1) is := by
  intro k hk s
  have := h (k + 1) (by simpa using hk) s
  rw [show pc + (k + 1) = pc + 1 + k by omega] at this
  simpa using this

/-- The head of a straight-line segment is the action at its first index. -/
theorem OpsAt.head {prog : List M.Instr} {pc : Nat} {i : M.Op} {is : List M.Op}
    (h : M.OpsAt prog pc (i :: is)) (s : M.MState) : M.act prog pc s = some (.op i) :=
  h 0 (Nat.succ_pos _) s

/-- **The machine reaches the end of a straight-line segment** in the state of the block
    fold. -/
theorem reaches_ops {prog : List M.Instr} :
    ∀ (ops : List M.Op) (pc : Nat) (s : M.MState), M.OpsAt prog pc ops →
      M.Reaches prog pc s (pc + ops.length) (M.runBlock s ops)
  | [], pc, s, _ => .refl pc s
  | i :: is, pc, s, h => by
      have hstep : M.mstep prog pc s = some (.go (pc + 1) (M.exec s i)) := by
        simp only [mstep, h.head s]
      have ih := reaches_ops is (pc + 1) (M.exec s i) h.tail
      rw [show pc + 1 + is.length = pc + (i :: is).length by simp; omega] at ih
      exact .next hstep ih

/-- **A straight-line segment followed by `ret` halts** in the state of the block fold. -/
theorem halts_ops {prog : List M.Instr} (ops : List M.Op) (pc : Nat) (s : M.MState)
    (h : M.OpsAt prog pc ops)
    (hret : M.act prog (pc + ops.length) (M.runBlock s ops) = some .ret) :
    M.Halts prog pc s (M.runBlock s ops) :=
  ⟨_, reaches_ops ops pc s h, hret⟩

/-- **The leakage of a straight-line segment followed by `ret`** is the leakage of the
    block, under a side condition every operation of the block satisfies. -/
theorem runL_ops {ok : M.MState → M.Op → Prop} {prog : List M.Instr} :
    ∀ (ops : List M.Op) (pc : Nat) (s : M.MState), M.OpsAt prog pc ops → M.BlockOk ok s ops →
      M.act prog (pc + ops.length) (M.runBlock s ops) = some .ret →
      M.RunL ok prog pc s (M.blockLeak s ops) (M.runBlock s ops)
  | [], _, _, _, _, hret => .ret hret
  | i :: is, pc, s, h, hok, hret => by
      rw [show pc + (i :: is).length = pc + 1 + is.length by simp; omega] at hret
      have ih := runL_ops is (pc + 1) (M.exec s i) h.tail hok.2 hret
      have := RunL.op (h.head s) hok.1 ih
      simpa [blockLeak, runBlock] using this

end IsaMachine

/-- **The target index of a relative branch over 4-byte words**: the branch at index `pc`
    with the signed byte displacement `off` reaches the index `pc + off / 4`, when `off` is a
    multiple of 4 and the index is not negative. -/
def wordTarget (pc : Nat) (off : Int) : Option Nat :=
  if off % 4 = 0 ∧ 0 ≤ (pc : Int) + off / 4 then some ((pc : Int) + off / 4).toNat else none

/-- The byte address of the target of a relative branch is the byte address of the branch
    plus the displacement, modulo `2⁶⁴`. -/
theorem wordTarget_ofNat {pc : Nat} {off : Int} {tgt : Nat} (h : wordTarget pc off = some tgt)
    (base : BitVec 64) :
    base + BitVec.ofNat 64 (4 * tgt) = base + BitVec.ofNat 64 (4 * pc) + BitVec.ofInt 64 off := by
  unfold wordTarget at h
  split at h
  · rename_i hc
    obtain ⟨h4, h0⟩ := hc
    simp only [Option.some.injEq] at h
    have e : ((4 * tgt : Nat) : Int) = ((4 * pc : Nat) : Int) + off := by
      rw [← h]
      push_cast
      rw [Int.toNat_of_nonneg h0]
      omega
    rw [BitVec.add_assoc]
    congr 1
    rw [← BitVec.ofInt_natCast, e, BitVec.ofInt_add, BitVec.ofInt_natCast]
  · cases h

end CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
