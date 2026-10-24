/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.YmmRegAlloc

/-!
# Vector instruction selection: rotates and three-input logic

A peephole pass over `List YmmInstr` that replaces two instruction idioms with
single AVX-512VL instructions:

* **Rotate.** `t₁ := vpsllq k x`, `t₂ := vpsrlq (64 - k) x`, `d := vpor t₁ t₂`
  becomes `d := vprolq k x`.
* **And-not-xor.** `t := vpandn b c`, `d := vpxor a t` becomes
  `d := vpternlogq 0xD2 d b c` when `d` is `a`, or `vmovdqu a → d` followed by
  it when `d` is distinct from `a`, `b` and `c`.

Either idiom is rewritten only when its temporaries are read by no later
instruction, so removing them changes no value any later instruction sees. The
checks are conservative: a temporary read anywhere later blocks the rewrite,
whatever redefines it first.

The pass is generic over the instruction stream; it has no knowledge of the
program it runs on.

## Soundness

`ymmStep` and `ymmRun` give `YmmInstr` its semantics over a named register file
and a memory indexed by `YmmMem`: an ALU instruction applies `YmmOp.denote` to
its operands, `vpternlogq` applies `ternlogW`, and the moves copy between
registers and memory. `selectYmm_sound` states that the selected program and
the input program, run from the same state, end with the same memory and the
same value in every register that is not the destination of a `vpsllq`,
`vpsrlq` or `vpandn` of the input (`selectTemps`). No side condition is needed:
the pass checks liveness inside the list itself, and the registers it may leave
with a different final value are exactly the removed temporaries.

The proof is a simulation. `selectYmm_agreeOff` carries the invariant that the
two states agree on memory and on every register outside a set none of whose
members the remaining input reads. The value lemmas are `vprolqW_eq_vporW`
(built lane by lane from `qword_rotl_eq_shiftOr`) for the rotate and
`chi_is_ternlog_d2` for the and-not-xor. The immediate `0xD2` is the truth
table of `a ^ (~b & c)`, which is Keccak's chi step.

The typed `Com` peephole frameworks (`VIR/Peephole.lean`,
`Optimizer/Rewrite/Peephole.lean`) do not apply here: `YmmInstr` programs are
not in SSA form, they name mutable registers, and `vpternlogq` reads its
destination.

## Main definitions

* `readsLater`: whether a name is read by any instruction in a suffix.
* `selectYmm`: the peephole.
* `YmmState`, `ymmStep`, `ymmRun`: the semantics of `YmmInstr` programs.
* `selectTemps`: the registers the pass may leave with a different value.

## Main results

* `qword_rotl_eq_shiftOr`, `vprolqW_eq_vporW`, `chi_is_ternlog_d2`: the value
  identities.
* `selectYmm_agreeOff`: the simulation invariant.
* `selectYmm_sound`: the whole-list soundness of the pass.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.YmmSelect

open CatCrypt.Crypto.SecureCompilation.VIR.YmmAsmPrint
open CatCrypt.Crypto.SecureCompilation.VIR.YmmRegAlloc
open CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect

/-- The truth table of `a ^ (~b & c)` with `a` the high input: Keccak's chi. -/
def chiImm : Nat := 0xD2

/-- Whether `n` is read by any instruction of `rest`. -/
def readsLater (n : String) (rest : List YmmInstr) : Bool :=
  rest.any (fun i => (ymmReadNames i).contains n)

/-- Whether the three instructions `t₁ := vpsllq k x`, `t₂ := vpsrlq k₂ x₂`,
    `d := vpor srcs`, followed by `rest`, form a rotate the pass may fuse. -/
def rotateOk (k k₂ : Nat) (t₁ t₂ x x₂ : String) (srcs : List String)
    (rest : List YmmInstr) : Bool :=
  x == x₂ && k + k₂ == 64 && 0 < k && k < 64
    && (srcs == [t₁, t₂] || srcs == [t₂, t₁])
    && t₁ != t₂ && t₁ != x && t₂ != x
    && !readsLater t₁ rest && !readsLater t₂ rest

/-- The replacement for `t := vpandn b c`, `d := vpxor srcs`, if the pair is an
    and-not-xor the pass may fuse; `none` otherwise. -/
def chiRewrite (t b c d : String) (srcs : List String) (rest : List YmmInstr) :
    Option (List YmmInstr) :=
  let a? : Option String :=
    match srcs with
    | [p, q] => if q == t then some p else if p == t then some q else none
    | _ => none
  match a? with
  | none => none
  | some a =>
    if t == a || t == b || t == c || readsLater t rest then none
    else if d == a then some [.ternlog chiImm d b c]
    else if d == b || d == c then none
    else some [.ymov d a, .ternlog chiImm d b c]

/-- The peephole. Each rewrite consumes its whole idiom; otherwise the head
    instruction is kept and the pass moves one instruction on. -/
def selectYmm : List YmmInstr → List YmmInstr
  | (.alu (.vpsllq k) t₁ [x]) :: (.alu (.vpsrlq k₂) t₂ [x₂]) :: (.alu .vpor d srcs) :: rest =>
      if rotateOk k k₂ t₁ t₂ x x₂ srcs rest then
        .alu (.vprolq k) d [x] :: selectYmm rest
      else
        .alu (.vpsllq k) t₁ [x] ::
          selectYmm ((.alu (.vpsrlq k₂) t₂ [x₂]) :: (.alu .vpor d srcs) :: rest)
  | (.alu .vpandn t [b, c]) :: (.alu .vpxor d srcs) :: rest =>
      match chiRewrite t b c d srcs rest with
      | some out => out ++ selectYmm rest
      | none => .alu .vpandn t [b, c] :: selectYmm ((.alu .vpxor d srcs) :: rest)
  | i :: rest => i :: selectYmm rest
  | [] => []
termination_by l => l.length

/-! ## The value identities -/

/-- A left rotate of a 64-bit lane is the OR of its two shifts. The rotate
    rewrite fuses exactly this triple, lane by lane. -/
theorem qword_rotl_eq_shiftOr (x : BitVec 64) (k : Nat) (hk : k < 64) :
    x.rotateLeft k = (x <<< k) ||| (x >>> (64 - k)) := by
  rw [BitVec.rotateLeft_def]
  simp [Nat.mod_eq_of_lt hk]

/-- `vpternlogq 0xD2` computes `a ^ (~b & c)` on all 256 bits: the and-not-xor
    rewrite replaces `vpandn` and `vpxor` by one instruction of the same value. -/
theorem chi_is_ternlog_d2 (a b c : BitVec 256) :
    ternlogW chiImm a b c = vpxorW a (vpandnW b c) := by
  simp only [chiImm, ternlogW, vpxorW, vpandnW, List.range, List.range.loop, List.foldl]
  simp (config := { decide := true })
  ext i hi
  simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_xor]
  cases a[i] <;> cases b[i] <;> cases c[i] <;> rfl

/-- Packing four qword lanes commutes with bitwise OR. -/
theorem yOfQwordsW_or (f g : Fin 4 → BitVec 64) :
    yOfQwordsW f ||| yOfQwordsW g = yOfQwordsW (fun j => f j ||| g j) := by
  have key : ∀ a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : BitVec 256,
      (0 ||| a₀ ||| a₁ ||| a₂ ||| a₃) ||| (0 ||| b₀ ||| b₁ ||| b₂ ||| b₃) =
        0 ||| (a₀ ||| b₀) ||| (a₁ ||| b₁) ||| (a₂ ||| b₂) ||| (a₃ ||| b₃) := by
    intros; ac_rfl
  simp only [yOfQwordsW, Fin.foldl_succ, Fin.foldl_zero, BitVec.setWidth_or,
    BitVec.shiftLeft_or_distrib]
  exact key _ _ _ _ _ _ _ _

/-- `vprolq k` on a 256-bit register is the OR of `vpsllq k` and
    `vpsrlq (64 - k)` of it, for `k < 64`: the value of the rotate rewrite. -/
theorem vprolqW_eq_vporW (v : BitVec 256) (k : Nat) (hk : k < 64) :
    vprolqW v k = vporW (vpsllqW v k) (vpsrlqW v (64 - k)) := by
  simp only [vprolqW, vporW, vpsllqW, vpsrlqW, yOfQwordsW_or,
    qword_rotl_eq_shiftOr _ _ hk]

/-! ## The semantics of `YmmInstr` programs -/

/-- A machine state for `YmmInstr` programs: the named vector registers and the
    256-bit memory cells addressed by `YmmMem`. -/
structure YmmState where
  /-- The value of each named vector register. -/
  regs : String → BitVec 256
  /-- The value of each memory cell. -/
  mem : YmmMem → BitVec 256

/-- The state with register `d` set to `v`. -/
def YmmState.setReg (s : YmmState) (d : String) (v : BitVec 256) : YmmState :=
  { s with regs := fun r => if r = d then v else s.regs r }

/-- The state with memory cell `m` set to `v`. -/
def YmmState.setMem (s : YmmState) (m : YmmMem) (v : BitVec 256) : YmmState :=
  { s with mem := fun m' => if m'.base = m.base ∧ m'.disp = m.disp then v else s.mem m' }

/-- The value an ALU instruction `op` computes from the registers `regs` on its
    operand list: a unary op reads its one operand, a binary op its two. An
    operand list of any other length, which the renderer rejects, yields zero. -/
def aluVal (op : YmmOp) (regs : String → BitVec 256) : List String → BitVec 256
  | [a] => op.denote (regs a) (regs a)
  | [a, b] => op.denote (regs a) (regs b)
  | _ => 0

/-- One instruction: an ALU op or `vpternlogq` writes its destination register,
    a move copies a register, a load a memory cell into a register, and a store
    a register into a memory cell. -/
def ymmStep : YmmInstr → YmmState → YmmState
  | .alu op d srcs, s => s.setReg d (aluVal op s.regs srcs)
  | .ymov d a, s => s.setReg d (s.regs a)
  | .yload d m, s => s.setReg d (s.mem m)
  | .ystore m a, s => s.setMem m (s.regs a)
  | .ternlog imm d b c, s => s.setReg d (ternlogW imm (s.regs d) (s.regs b) (s.regs c))

/-- A straight-line program, run instruction by instruction. -/
def ymmRun (l : List YmmInstr) (s : YmmState) : YmmState :=
  l.foldl (fun s i => ymmStep i s) s

@[simp] theorem ymmRun_nil (s : YmmState) : ymmRun [] s = s := rfl

@[simp] theorem ymmRun_cons (i : YmmInstr) (l : List YmmInstr) (s : YmmState) :
    ymmRun (i :: l) s = ymmRun l (ymmStep i s) := rfl

theorem ymmRun_append (l₁ l₂ : List YmmInstr) (s : YmmState) :
    ymmRun (l₁ ++ l₂) s = ymmRun l₂ (ymmRun l₁ s) := by
  simp [ymmRun, List.foldl_append]

/-! ## Soundness of the pass -/

/-- The destination of an instruction if it is a `vpsllq`, `vpsrlq` or
    `vpandn`, the three instructions whose result the pass may remove. -/
def selectTempDest : YmmInstr → List String
  | .alu (.vpsllq _) d _ => [d]
  | .alu (.vpsrlq _) d _ => [d]
  | .alu .vpandn d _ => [d]
  | _ => []

/-- The registers `selectYmm l` may leave with a value different from `l`'s:
    the destinations of the `vpsllq`, `vpsrlq` and `vpandn` instructions of `l`. -/
def selectTemps (l : List YmmInstr) : List String := l.flatMap selectTempDest

theorem selectTemps_cons (i : YmmInstr) (l : List YmmInstr) :
    selectTemps (i :: l) = selectTempDest i ++ selectTemps l := by
  simp [selectTemps]

/-- Two states agree on memory and on every register outside `P`. -/
def YmmAgreeOff (P : String → Prop) (s₁ s₂ : YmmState) : Prop :=
  s₁.mem = s₂.mem ∧ ∀ r, ¬ P r → s₁.regs r = s₂.regs r

theorem YmmAgreeOff.mono {P Q : String → Prop} {s₁ s₂ : YmmState}
    (h : YmmAgreeOff P s₁ s₂) (hPQ : ∀ r, P r → Q r) : YmmAgreeOff Q s₁ s₂ :=
  ⟨h.1, fun r hr => h.2 r (fun hp => hr (hPQ r hp))⟩

theorem aluVal_congr (op : YmmOp) {r₁ r₂ : String → BitVec 256} (srcs : List String)
    (h : ∀ a ∈ srcs, r₁ a = r₂ a) : aluVal op r₁ srcs = aluVal op r₂ srcs := by
  rcases srcs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp_all [aluVal]

/-- An instruction that reads no register of `P` preserves agreement outside
    `P`: `ymmStep` reads exactly `ymmReadNames`. -/
theorem ymmStep_agreeOff {P : String → Prop} {s₁ s₂ : YmmState} (i : YmmInstr)
    (h : YmmAgreeOff P s₁ s₂) (hr : ∀ r ∈ ymmReadNames i, ¬ P r) :
    YmmAgreeOff P (ymmStep i s₁) (ymmStep i s₂) := by
  obtain ⟨hm, hg⟩ := h
  have hg' : ∀ r ∈ ymmReadNames i, s₁.regs r = s₂.regs r := fun r h => hg r (hr r h)
  cases i with
  | alu op d srcs =>
    refine ⟨hm, fun r _ => ?_⟩
    simp only [ymmStep, YmmState.setReg]
    split_ifs
    · exact aluVal_congr op srcs hg'
    · exact hg r ‹_›
  | ymov d a =>
    refine ⟨hm, fun r _ => ?_⟩
    simp only [ymmStep, YmmState.setReg]
    split_ifs
    · exact hg' a (by simp [ymmReadNames])
    · exact hg r ‹_›
  | yload d m =>
    refine ⟨hm, fun r _ => ?_⟩
    simp only [ymmStep, YmmState.setReg, hm]
    split_ifs
    · rfl
    · exact hg r ‹_›
  | ystore m a =>
    refine ⟨?_, hg⟩
    simp only [ymmStep, YmmState.setMem, hm, hg' a (by simp [ymmReadNames])]
  | ternlog imm d b c =>
    refine ⟨hm, fun r _ => ?_⟩
    simp only [ymmStep, YmmState.setReg]
    split_ifs
    · simp only [hg' d (by simp [ymmReadNames]), hg' b (by simp [ymmReadNames]),
        hg' c (by simp [ymmReadNames])]
    · exact hg r ‹_›

theorem readsLater_cons (n : String) (i : YmmInstr) (l : List YmmInstr) :
    readsLater n (i :: l) = false ↔ n ∉ ymmReadNames i ∧ readsLater n l = false := by
  simp [readsLater]

/-- What an accepted rotate triple satisfies. -/
theorem rotateOk_spec {k k₂ : Nat} {t₁ t₂ x x₂ : String} {srcs : List String}
    {rest : List YmmInstr} (h : rotateOk k k₂ t₁ t₂ x x₂ srcs rest = true) :
    x₂ = x ∧ k₂ = 64 - k ∧ k < 64 ∧ (srcs = [t₁, t₂] ∨ srcs = [t₂, t₁]) ∧
      t₁ ≠ t₂ ∧ t₁ ≠ x ∧ t₂ ≠ x ∧ readsLater t₁ rest = false ∧
      readsLater t₂ rest = false := by
  simp only [rotateOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.or_eq_true,
    bne_iff_ne, ne_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hx, hk⟩, _⟩, hk64⟩, hs⟩, h12⟩, h1x⟩, h2x⟩, hr1⟩, hr2⟩ := h
  exact ⟨hx.symm, by omega, hk64, hs, h12, h1x, h2x, hr1, hr2⟩

/-- What an accepted and-not-xor pair satisfies, and its replacement. -/
theorem chiRewrite_spec {t b c d : String} {srcs : List String} {rest : List YmmInstr}
    {out : List YmmInstr} (h : chiRewrite t b c d srcs rest = some out) :
    ∃ a, (srcs = [a, t] ∨ srcs = [t, a]) ∧ t ≠ a ∧ t ≠ b ∧ t ≠ c ∧
      readsLater t rest = false ∧
      ((d = a ∧ out = [.ternlog chiImm d b c]) ∨
        (d ≠ a ∧ d ≠ b ∧ d ≠ c ∧ out = [.ymov d a, .ternlog chiImm d b c])) := by
  unfold chiRewrite at h
  obtain _ | ⟨p, _ | ⟨q, _ | ⟨_, _⟩⟩⟩ := srcs
  all_goals try (simp at h; done)
  by_cases hq : q = t
  · subst hq
    refine ⟨p, Or.inl rfl, ?_⟩
    simp only [beq_self_eq_true, ite_true, Bool.or_eq_true, beq_iff_eq] at h
    split_ifs at h with h1 h2 h3 <;> simp_all
  · by_cases hp : p = t
    · subst hp
      refine ⟨q, Or.inr rfl, ?_⟩
      simp only [beq_iff_eq, hq, ite_false, beq_self_eq_true, ite_true, Bool.or_eq_true] at h
      split_ifs at h with h1 h2 h3 <;> simp_all
    · simp [hp, hq] at h

/-- A kept head instruction preserves the invariant of `selectYmm_agreeOff`. -/
theorem ymmStep_agreeOff_cons {P : String → Prop} {s₁ s₂ : YmmState} (i : YmmInstr)
    (l : List YmmInstr) (h : YmmAgreeOff P s₁ s₂)
    (hP : ∀ r, P r → readsLater r (i :: l) = false) :
    YmmAgreeOff P (ymmStep i s₁) (ymmStep i s₂) ∧ ∀ r, P r → readsLater r l = false := by
  refine ⟨ymmStep_agreeOff i h fun r hr hp => ?_,
    fun r hp => ((readsLater_cons _ _ _).1 (hP r hp)).2⟩
  exact ((readsLater_cons _ _ _).1 (hP r hp)).1 hr

/-- The simulation invariant of the pass. If two states agree outside `P` and
    `l` reads no register of `P`, running `selectYmm l` from the first and `l`
    from the second ends in states that agree outside `P` and `selectTemps l`. -/
theorem selectYmm_agreeOff (l : List YmmInstr) :
    ∀ (P : String → Prop) (s₁ s₂ : YmmState), YmmAgreeOff P s₁ s₂ →
      (∀ r, P r → readsLater r l = false) →
      YmmAgreeOff (fun r => P r ∨ r ∈ selectTemps l)
        (ymmRun (selectYmm l) s₁) (ymmRun l s₂) := by
  fun_induction selectYmm l
  all_goals intro P s₁ s₂ h hP
  case case1 k t₁ x k₂ t₂ x₂ d srcs rest hok ih =>
    obtain ⟨hxx, rfl, hk, hs, h12, h1x, h2x, hr1, hr2⟩ := rotateOk_spec hok
    subst x₂
    have hx : ¬ P x := fun hp => by
      have := hP x hp
      simp [readsLater, ymmReadNames] at this
    have hxs : s₁.regs x = s₂.regs x := h.2 x hx
    have hmid : YmmAgreeOff (fun r => P r ∨ r = t₁ ∨ r = t₂)
        (ymmStep (.alu (.vprolq k) d [x]) s₁)
        (ymmStep (.alu .vpor d srcs) (ymmStep (.alu (.vpsrlq (64 - k)) t₂ [x])
          (ymmStep (.alu (.vpsllq k) t₁ [x]) s₂))) := by
      refine ⟨h.1, fun r hr => ?_⟩
      have hr' : s₁.regs r = s₂.regs r := h.2 r (fun hp => hr (Or.inl hp))
      rcases hs with rfl | rfl
      · simp only [ymmStep, YmmState.setReg, aluVal, YmmOp.denote, YmmOp.denoteBinary]
        split_ifs <;> simp_all [vprolqW_eq_vporW _ _ hk]
      · simp only [ymmStep, YmmState.setReg, aluVal, YmmOp.denote, YmmOp.denoteBinary]
        split_ifs <;> simp_all [vprolqW_eq_vporW _ _ hk, vporW, BitVec.or_comm]
    have hP' : ∀ r, (P r ∨ r = t₁ ∨ r = t₂) → readsLater r rest = false := by
      rintro r (hp | rfl | rfl)
      · have := hP r hp
        simp only [readsLater_cons] at this
        exact this.2.2.2
      · exact hr1
      · exact hr2
    simp only [ymmRun_cons]
    refine (ih _ _ _ hmid hP').mono fun r hr => ?_
    simp only [selectTemps_cons, selectTempDest, List.mem_append, List.mem_singleton,
      List.not_mem_nil] at hr ⊢
    tauto
  case case3 t b c d srcs rest out hout ih =>
    obtain ⟨a, hs, hta, htb, htc, hrt, hout'⟩ := chiRewrite_spec hout
    have hread : ∀ n, n = a ∨ n = b ∨ n = c → ¬ P n := by
      rintro n hn hp
      have := hP n hp
      rcases hs with rfl | rfl <;>
        simp [readsLater, ymmReadNames] at this <;> tauto
    have ha := h.2 a (hread a (Or.inl rfl))
    have hb := h.2 b (hread b (Or.inr (Or.inl rfl)))
    have hc := h.2 c (hread c (Or.inr (Or.inr rfl)))
    have hmid : YmmAgreeOff (fun r => P r ∨ r = t) (ymmRun out s₁)
        (ymmStep (.alu .vpxor d srcs) (ymmStep (.alu .vpandn t [b, c]) s₂)) := by
      refine ⟨?_, fun r hr => ?_⟩
      · rcases hout' with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;>
          simpa [ymmStep, YmmState.setReg] using h.1
      · have hr' : s₁.regs r = s₂.regs r := h.2 r (fun hp => hr (Or.inl hp))
        rcases hout' with ⟨rfl, rfl⟩ | ⟨hda, hdb, hdc, rfl⟩ <;> rcases hs with rfl | rfl <;>
          simp only [ymmRun_cons, ymmRun_nil, ymmStep, YmmState.setReg, aluVal, YmmOp.denote,
            YmmOp.denoteBinary] <;>
          split_ifs <;> simp_all [chi_is_ternlog_d2, vpxorW, BitVec.xor_comm]
    have hP' : ∀ r, (P r ∨ r = t) → readsLater r rest = false := by
      rintro r (hp | rfl)
      · have := hP r hp
        simp only [readsLater_cons] at this
        exact this.2.2
      · exact hrt
    rw [ymmRun_append]
    simp only [ymmRun_cons]
    refine (ih _ _ _ hmid hP').mono fun r hr => ?_
    simp only [selectTemps_cons, selectTempDest, List.mem_append, List.mem_singleton,
      List.not_mem_nil] at hr ⊢
    tauto
  case case6 => exact h.mono fun r hr => Or.inl hr
  all_goals
    rename_i ih
    obtain ⟨h1, h2⟩ := ymmStep_agreeOff_cons _ _ h hP
    simp only [ymmRun_cons]
    refine (ih _ _ _ h1 h2).mono fun r hr => ?_
    rw [selectTemps_cons, List.mem_append]
    tauto

/-- **Soundness of `selectYmm`.** Run from the same state, the selected program
    and the input program end with the same memory and the same value in every
    register outside `selectTemps l`. -/
theorem selectYmm_sound (l : List YmmInstr) (s : YmmState) :
    (ymmRun (selectYmm l) s).mem = (ymmRun l s).mem ∧
      ∀ r, r ∉ selectTemps l → (ymmRun (selectYmm l) s).regs r = (ymmRun l s).regs r := by
  have := selectYmm_agreeOff l (fun _ => False) s s ⟨rfl, fun _ _ => rfl⟩ (fun _ h => h.elim)
  exact ⟨this.1, fun r hr => this.2 r (by simp [hr])⟩

end CatCrypt.Crypto.SecureCompilation.VIR.YmmSelect
