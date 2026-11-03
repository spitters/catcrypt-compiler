/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFGMemF
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
public import CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa

@[expose] public section

set_option autoImplicit false

/-!
# Conditional jumps whose condition is a constant

A conditional jump of the flag machine at position `k` of a body whose two predecessors are
the move of an immediate `c` into a register `r` and the compare of `r` with an immediate
`c'`,

```
k - 2 : MOV:64 r, #c
k - 1 : CMP:64 r, #c'
k     : Lcond cc l
```

jumps on every run that reaches `k` from the entry, or on none, by the value of
`c = c'` at 64 bits and the polarity of `cc`. A jump lands one past a label, and the two
instructions before `k` are no labels, so `k` is entered only through `k - 2` and `k - 1`.
The arm-end guard of `ExportRegions.ifFrame` at `x86Data` (`MOV r, #1; CMP r, #0;
Lcond NZ`) is of this form and always jumps.

This module recognises the form (`constGuard?`, `constTakenB`) and states the invariant of
the flag machine that makes the recognition sound (`GuardInv`): it holds at position `0`,
every step keeps it, and at a constant-taken guard it gives the polarity of the zero flag.

## Main definitions

* `guardMovImm?`: the move of an immediate into a register with the register tag.
* `constGuard?`: the register, the two immediates and the polarity of a constant guard.
* `constTakenB`: the guard at a position jumps on every run that reaches it.
* `GuardInv`: the zero flag at a guard and the register before its compare hold the values
  of the two instructions before the guard.
* `TakenAt`: at a constant-taken guard the instruction is a flag conditional whose polarity
  is the zero flag.

## Main results

* `constGuard?_spec`: the shape of a recognised guard.
* `guardInv_zero`: the invariant holds at position `0`.
* `guardInv_step`, `guardInv_retRes`, `guardInv_isaStep`: a step of the flag machine, the
  result of a call, and a step of an instruction set whose further steps are local calls
  keep the invariant.
* `takenAt_of_guardInv`: under the invariant, the instruction at the position of the state
  satisfies `TakenAt`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ConstGuard

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (fstepF
  evalInstrPMemF_isLopn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG (NextPc
  evalInstrPMemF_next cmpArgs?_lopn)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa callShadow retRes shadowCall?
  shadowCall?_callShadow lpc_retRes)

/-! ## 1. The recogniser -/

/-- The move `MOV:64 r, #c` of an immediate into a register with the register tag: the
    register and the immediate. -/
def guardMovImm? : LinstrRM → Option (String × Nat)
  | (.Lopn [.reg r] opn [.imm c], .reg none) =>
      if opn = withWidthTag 64 "MOV" then some (r, c) else none
  | _ => none

/-- **A constant guard at position `k` of `body`**: the instruction at `k` is a flag
    conditional of polarity `pol`, the instruction at `k - 1` compares the register `r` with
    the immediate `c'`, and the instruction at `k - 2` moves the immediate `c` into `r`. -/
def constGuard? (body : List LinstrRM) : Nat → Option (String × Nat × Nat × Bool)
  | k + 2 =>
      match body[k]?, body[k + 1]?, body[k + 2]? with
      | some m, some j, some l =>
          match guardMovImm? m, cmpArgs? j, flagCondCC? l with
          | some (r, c), some (.reg r', .imm c'), some (pol, _) =>
              if r' = r then some (r, c, c', pol) else none
          | _, _, _ => none
      | _, _, _ => none
  | _ => none

/-- **The guard at position `k` jumps on every run that reaches it**: it is a constant guard
    whose compare sets the zero flag to the polarity of its conditional. -/
def constTakenB (body : List LinstrRM) (k : Nat) : Bool :=
  match constGuard? body k with
  | some (_, c, c', pol) => (BitVec.ofNat 64 c == BitVec.ofNat 64 c') == pol
  | none => false

theorem guardMovImm?_spec {m : LinstrRM} {r : String} {c : Nat}
    (h : guardMovImm? m = some (r, c)) :
    m = (.Lopn [.reg r] (withWidthTag 64 "MOV") [.imm c], .reg none) := by
  unfold guardMovImm? at h
  split at h
  · split at h
    · cases h
      subst_vars
      rfl
    · cases h
  · cases h

/-- **The shape of a constant guard.** -/
theorem constGuard?_spec {body : List LinstrRM} {k : Nat} {r : String} {c c' : Nat}
    {pol : Bool} (h : constGuard? body k = some (r, c, c', pol)) :
    ∃ k0, k = k0 + 2
      ∧ body[k0]? = some (.Lopn [.reg r] (withWidthTag 64 "MOV") [.imm c], .reg none)
      ∧ (∃ j, body[k0 + 1]? = some j ∧ cmpArgs? j = some (.reg r, .imm c'))
      ∧ ∃ l lbl, body[k0 + 2]? = some l ∧ flagCondCC? l = some (pol, lbl) := by
  match k, h with
  | k0 + 2, h =>
    refine ⟨k0, rfl, ?_⟩
    rcases hm : body[k0]? with _ | m
    · simp [constGuard?, hm] at h
    rcases hj : body[k0 + 1]? with _ | j
    · simp [constGuard?, hm, hj] at h
    rcases hl : body[k0 + 2]? with _ | l
    · simp [constGuard?, hm, hj, hl] at h
    rcases hm' : guardMovImm? m with _ | ⟨r1, c1⟩
    · simp [constGuard?, hm, hj, hl, hm'] at h
    rcases hj' : cmpArgs? j with _ | ⟨a, b⟩
    · simp [constGuard?, hm, hj, hl, hm', hj'] at h
    rcases hl' : flagCondCC? l with _ | ⟨pol1, lbl⟩
    · cases a <;> cases b <;> simp [constGuard?, hm, hj, hl, hm', hj', hl'] at h
    cases a with
    | reg r' =>
      cases b with
      | imm c1' =>
        simp only [constGuard?, hm, hj, hl, hm', hj', hl'] at h
        by_cases hr : r' = r1
        · subst hr
          simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact ⟨by rw [guardMovImm?_spec hm'], ⟨j, rfl, hj'⟩, l, lbl, rfl, hl'⟩
        · simp [hr] at h
      | _ => simp [constGuard?, hm, hj, hl, hm', hj', hl'] at h
    | _ => cases b <;> simp [constGuard?, hm, hj, hl, hm', hj', hl'] at h

/-! ## 2. The invariant -/

/-- **The invariant of a constant guard** at a state `s` of a run on `body`: at a constant
    guard at the position of `s`, the zero flag is the value of its compare; at a constant
    guard one past the position of `s`, the register of its compare holds the immediate of
    its move. -/
def GuardInv (body : List LinstrRM) (s : LstateMF) : Prop :=
  (∀ r c c' pol, constGuard? body s.prog.base.lpc = some (r, c, c', pol) →
      s.zf = (BitVec.ofNat 64 c == BitVec.ofNat 64 c'))
  ∧ ∀ r c c' pol, constGuard? body (s.prog.base.lpc + 1) = some (r, c, c', pol) →
      evalOperandN s.prog.base.reg 64 (.reg r) = some (BitVec.ofNat 64 c)

/-- **A constant-taken guard jumps**: when the guard at the position of `s` is constant-taken,
    the instruction `i` is a flag conditional whose polarity is the zero flag of `s`. -/
def TakenAt (body : List LinstrRM) (i : LinstrRM) (s : LstateMF) : Prop :=
  constTakenB body s.prog.base.lpc = true → ∃ lbl, flagCondCC? i = some (s.zf, lbl)

/-- **The invariant at the entry.** A constant guard is at a position of at least `2`. -/
theorem guardInv_zero (body : List LinstrRM) {s : LstateMF} (h : s.prog.base.lpc = 0) :
    GuardInv body s := by
  rw [GuardInv, h]
  exact ⟨fun _ _ _ _ h => by simp [constGuard?] at h,
    fun _ _ _ _ h => by simp [constGuard?] at h⟩

/-- **The polarity at a constant-taken guard.** -/
theorem takenAt_of_guardInv {body : List LinstrRM} {i : LinstrRM} {s : LstateMF}
    (hg : GuardInv body s) (hb : body[s.prog.base.lpc]? = some i) : TakenAt body i s := by
  intro ht
  unfold constTakenB at ht
  split at ht
  · rename_i r c c' pol hc
    obtain ⟨k0, hk, -, -, l, lbl, hl, hl'⟩ := constGuard?_spec hc
    rw [← hk, hb] at hl
    cases hl
    have hz := hg.1 r c c' pol hc
    have hp : (BitVec.ofNat 64 c == BitVec.ofNat 64 c') = pol := by simpa using ht
    refine ⟨lbl, ?_⟩
    rw [hl', hz, hp]
  · cases ht

/-- A move of an immediate is no label. -/
theorem not_label_movImm {r : String} {c : Nat} {a : LabelKind} {l : LLabel} :
    LinstrR.Lopn [.reg r] (withWidthTag 64 "MOV") [.imm c] ≠ .Llabel a l := nofun

/-- **Where a step lands**: one past its position, or one past a label of the body. -/
theorem land_of_nextPc {body : List LinstrRM} {w : LinstrR} {k k' : Nat}
    (h : NextPc (body.map Prod.fst) w k k') :
    k' = k + 1 ∨ ∃ q j a l, k' = q + 1 ∧ body[q]? = some j ∧ j.1 = .Llabel a l := by
  have hlab : ∀ l q, JasminLsemLabeled.findLabel l (body.map Prod.fst) = some q →
      ∃ j a l', body[q]? = some j ∧ j.1 = .Llabel a l' := by
    intro l q hq
    obtain ⟨x, hx, hl⟩ := JasminLsemLabeled.findLabel_sound l _ q hq
    rw [List.getElem?_map] at hx
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp hx
    unfold JasminLsemLabeled.isLabel at hl
    split at hl
    · rename_i a l' he
      exact ⟨j, a, l', hj, he⟩
    · cases hl
  cases w with
  | Lgoto x =>
      obtain ⟨f, l⟩ := x
      obtain ⟨q, hq, rfl⟩ := h
      obtain ⟨j, a, l', hj, he⟩ := hlab l q hq
      exact Or.inr ⟨q, j, a, l', rfl, hj, he⟩
  | Lcond c l =>
      rcases h with rfl | ⟨q, hq, rfl⟩
      · exact Or.inl rfl
      · obtain ⟨j, a, l', hj, he⟩ := hlab l q hq
        exact Or.inr ⟨q, j, a, l', rfl, hj, he⟩
  | Lret => exact absurd h id
  | _ => exact Or.inl h

/-- **The invariant is kept by a step** that lands as a step of the flag machine does, sets
    the zero flag at a compare of a register with an immediate as the flag machine does, and
    writes the immediate of a move into its register. -/
theorem guardInv_of_land {body : List LinstrRM} {i : LinstrRM} {s t : LstateMF}
    (hg : GuardInv body s) (hb : body[s.prog.base.lpc]? = some i)
    (hland : t.prog.base.lpc = s.prog.base.lpc + 1
      ∨ ∃ q j a l, t.prog.base.lpc = q + 1 ∧ body[q]? = some j ∧ j.1 = .Llabel a l)
    (hcmp : ∀ r c', cmpArgs? i = some (.reg r, .imm c') →
      t.prog.base.lpc = s.prog.base.lpc + 1 →
      ∀ v, evalOperandN s.prog.base.reg 64 (.reg r) = some v →
        t.zf = (v == BitVec.ofNat 64 c'))
    (hmov : ∀ r c, i = (.Lopn [.reg r] (withWidthTag 64 "MOV") [.imm c], .reg none) →
      t.prog.base.lpc = s.prog.base.lpc + 1 →
      evalOperandN t.prog.base.reg 64 (.reg r) = some (BitVec.ofNat 64 c)) :
    GuardInv body t := by
  constructor
  · intro r c c' pol hc
    obtain ⟨k0, hk, hm, ⟨j, hj, hj'⟩, -⟩ := constGuard?_spec hc
    obtain ⟨d, o, x, hjo⟩ := cmpArgs?_lopn hj'
    have hs : s.prog.base.lpc = k0 + 1 := by
      rcases hland with h1 | ⟨q, j', a, l, h1, h2, h3⟩
      · omega
      · have hq : q = k0 + 1 := by omega
        rw [hq, hj] at h2
        cases h2
        rw [hjo] at h3
        cases h3
    have hi : i = j := by
      rw [hs, hj] at hb
      exact (Option.some.inj hb).symm
    subst hi
    have hv := hg.2 r c c' pol (by rw [hs, ← hk]; exact hc)
    exact hcmp r c' hj' (by omega) _ hv
  · intro r c c' pol hc
    obtain ⟨k0, hk, hm, -, -⟩ := constGuard?_spec hc
    have hs : s.prog.base.lpc = k0 := by
      rcases hland with h1 | ⟨q, j', a, l, h1, h2, h3⟩
      · omega
      · have hq : q = k0 := by omega
        rw [hq, hm] at h2
        cases h2
        exact absurd h3 not_label_movImm
    have hi : i = (.Lopn [.reg r] (withWidthTag 64 "MOV") [.imm c], .reg none) := by
      rw [hs, hm] at hb
      exact (Option.some.inj hb).symm
    exact hmov r c hi (by omega)

/-- **A step of the flag machine keeps the invariant.** -/
theorem guardInv_step {fn : String} {body : List LinstrRM} {i : LinstrRM} {s t : LstateMF}
    (hg : GuardInv body s) (hb : body[s.prog.base.lpc]? = some i)
    (h : evalInstrPMemF (singletonProgM fn body) i s = some t) : GuardInv body t := by
  refine guardInv_of_land hg hb (land_of_nextPc (evalInstrPMemF_next _ i s t h).2) ?_ ?_
  · intro r c' hc _ v hv
    unfold evalInstrPMemF at h
    rw [hc] at h
    simp only [evalOperandN] at hv h
    rw [hv] at h
    simp only [Option.some.injEq] at h
    rw [← h]
  · intro r c hi _
    subst hi
    rw [evalInstrPMemF_isLopn _ _ _ ⟨_, _, _, rfl⟩] at h
    have hf : fstepF (.Lopn [.reg r] (withWidthTag 64 "MOV") [.imm c], .reg none)
        s.prog.base s.zf = some ((s.prog.base.setReg r (BitVec.ofNat 64 c)).nextPc, s.zf) :=
      rfl
    rw [hf] at h
    cases h
    simp [evalOperandN, LstateM.reg_nextPc, LstateM.reg_setReg]

/-- A compare is no shadow instruction of a call. -/
theorem shadowCall?_of_cmpArgs? {i : LinstrRM} {a b : LOperand}
    (h : cmpArgs? i = some (a, b)) : shadowCall? i.1 = none := by
  obtain ⟨w, tag⟩ := i
  unfold cmpArgs? at h
  split at h
  · rename_i x opn a' b' hw
    split at h
    · rename_i ho
      simp only at hw
      subst hw ho
      rcases x with _ | _ | _ | _ <;> simp [shadowCall?, withWidthTag]
    · cases h
  · cases h

/-- **The result of a call keeps the invariant.** A call is neither a compare nor a move of
    an immediate. -/
theorem guardInv_retRes {body : List LinstrRM} {i : LinstrRM} {s : LstateMF}
    {dst f : String} {srcs : List LOperand} {x : LprogIsa.CallRes}
    (hg : GuardInv body s) (hb : body[s.prog.base.lpc]? = some i)
    (hi : i.1 = callShadow dst f srcs) : GuardInv body (retRes dst x s) := by
  have hsc : shadowCall? i.1 = some (dst, f, srcs) := by rw [hi, shadowCall?_callShadow]
  refine guardInv_of_land hg hb (Or.inl (lpc_retRes dst x s)) ?_ ?_
  · intro r c' hc
    rw [shadowCall?_of_cmpArgs? hc] at hsc
    cases hsc
  · intro r c he
    rw [he] at hsc
    simp [shadowCall?, withWidthTag] at hsc

/-- **A step of an instruction set whose further steps are local calls keeps the
    invariant.** -/
theorem guardInv_isaStep {I : Isa} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (hcl : I.CallLocal X86Isa.x86Isa aa ao) {fn : String}
    {body : List LinstrRM} {i : LinstrRM} {s t : LstateMF}
    (hg : GuardInv body s) (hb : body[s.prog.base.lpc]? = some i)
    (h : I.step (singletonProgM fn body) i s = some t) : GuardInv body t := by
  rcases hcl _ i s t h with hx | ⟨dst, f, srcs, x, hi, rfl, -, -⟩
  · exact guardInv_step hg hb hx
  · exact guardInv_retRes hg hb hi

end CatCrypt.Crypto.SecureCompilation.X86Backend.ConstGuard
