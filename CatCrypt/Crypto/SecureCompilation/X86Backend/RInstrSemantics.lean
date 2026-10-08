/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow

/-!
# A step semantics for the decoded programs of `LprogBytesDecode`

`LprogBytesDecode.decodeLprog` returns a `List RInstr`: straight-line `JInstr 64`
instructions, conditional branches to instruction indices, and `ret`. This module
runs such a program on a machine given by the effect of one `JInstr 64` and the
name-keyed view whose flags the branches read (`Machine`). The program counter
indexes the list; a branch takes its target when Jasmin's condition
`JState.condB` holds for the SDM nibble (`condtOfNibble`), `ret` halts, and a
program counter outside the list, or a nibble without a condition, is stuck.

`Reaches M prog pc s pc' s'` is the reflexive-transitive closure of one step, and
`HaltsNoCall` is reaching a `ret` by steps. `step` is stuck at a `call`; `HaltsC` runs
through calls, each callee a nested run from its target to its own `ret`, and `Halts` is
`HaltsC` (`halts_of_haltsNoCall` embeds the call-free runs, `halts_of_reaches` builds a
halting run from a path to a `ret`). Two shape lemmas give the semantics of the two
segment forms the encoder lays down: a run of `op`s is the block fold
(`reaches_ops`), and the segment `body ++ [cmp ctr, 0] ++ [jne head]` is the
counted loop `Machine.runXLoop` (`reaches_xloop`). The name-keyed machine
`jMachine` runs `evalInstr`, and its block and loop are `runBlock` and
`LprogControlFlow.runXLoop`.

## Main results

* `run_of_haltsNoCall`: a call-free halting run is a `run` with enough fuel.
* `Halts`, `halts_of_haltsNoCall`, `halts_of_reaches`: the halting runs through calls and
  the embedding of the call-free runs.
* `reaches_ops`: from the first index of a segment `xs.map .op`, the machine reaches
  the index after the segment in the state `Machine.runBlock s xs`.
* `reaches_xloop`: from the first index of the segment
  `(l.body ++ [l.cmpInstr]).map .op ++ [.jcc 5 head]` with `head` that index, a
  terminating `Machine.runXLoop fuel s l = some s'` reaches the index after the
  segment in `s'`.
* `jMachine_runBlock`, `jMachine_runXLoop`: on `jMachine` the block fold is `runBlock`
  and the loop is `runXLoop`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr)

/-! ## 1. Machines and one step -/

/-- A machine a decoded program runs on: the effect of one straight-line
    instruction and the name-keyed view whose flags the branches read. -/
structure Machine (σ : Type) where
  /-- The effect of one `JInstr 64`. -/
  exec : σ → JInstr 64 → σ
  /-- The name-keyed view of a state; branches read its flags. -/
  view : σ → JState 64

/-- The condition of an SDM `Jcc` nibble: Jasmin's `Condt` in declaration order. -/
def condtOfNibble : Nat → Option Condt
  | 0 => some .o | 1 => some .no | 2 => some .b | 3 => some .nb
  | 4 => some .e | 5 => some .ne | 6 => some .be | 7 => some .nbe
  | 8 => some .s | 9 => some .ns | 10 => some .p | 11 => some .np
  | 12 => some .l | 13 => some .nl | 14 => some .le | 15 => some .nle
  | _ => none

/-- The outcome of one step: continue at a program counter, or halt at `ret`. -/
inductive Next (σ : Type) where
  | go (pc : Nat) (s : σ)
  | halt (s : σ)

variable {σ : Type}

/-- One step of `prog` at `pc`: an `op` runs and advances, `ret` halts, a branch
    goes to its target when its condition holds on the view's flags and advances
    otherwise, and `push`/`pop` run their straight-line effect (`pushOps`, `popOps`)
    and advance. A program counter outside `prog`, a nibble without a condition, and
    a `call` are stuck. -/
def step (M : Machine σ) (prog : List RInstr) (pc : Nat) (s : σ) : Option (Next σ) :=
  match prog[pc]? with
  | none => none
  | some (.op i) => some (.go (pc + 1) (M.exec s i))
  | some .ret => some (.halt s)
  | some (.jcc cc t) =>
      (condtOfNibble cc).map fun c => if (M.view s).condB c then .go t s else .go (pc + 1) s
  | some (.push r) => some (.go (pc + 1) ((LprogBytesDecode.pushOps r).foldl M.exec s))
  | some (.pop r) => some (.go (pc + 1) ((LprogBytesDecode.popOps r).foldl M.exec s))
  | some (.call _) => none

/-- Run `prog` from `pc` for at most `fuel` steps; the state at `ret`. -/
def run (M : Machine σ) (prog : List RInstr) : Nat → Nat → σ → Option σ
  | 0, _, _ => none
  | fuel + 1, pc, s =>
    match step M prog pc s with
    | none => none
    | some (.halt s') => some s'
    | some (.go pc' s') => run M prog fuel pc' s'

theorem run_go (M : Machine σ) (prog : List RInstr) (fuel pc pc' : Nat) (s s' : σ)
    (h : step M prog pc s = some (.go pc' s')) :
    run M prog (fuel + 1) pc s = run M prog fuel pc' s' := by
  simp [run, h]

theorem run_ret (M : Machine σ) (prog : List RInstr) (fuel pc : Nat) (s : σ)
    (h : prog[pc]? = some .ret) : run M prog (fuel + 1) pc s = some s := by
  simp [run, step, h]

/-! ## 2. Reachability -/

/-- The reflexive-transitive closure of `step` on continuing outcomes. -/
inductive Reaches (M : Machine σ) (prog : List RInstr) : Nat → σ → Nat → σ → Prop
  | refl (pc : Nat) (s : σ) : Reaches M prog pc s pc s
  | next {pc : Nat} {s : σ} {pc' : Nat} {s' : σ} {pc'' : Nat} {s'' : σ}
      (h : step M prog pc s = some (.go pc' s')) (hr : Reaches M prog pc' s' pc'' s'') :
      Reaches M prog pc s pc'' s''

theorem Reaches.trans {M : Machine σ} {prog : List RInstr} {pc : Nat} {s : σ} {pc' : Nat}
    {s' : σ} {pc'' : Nat} {s'' : σ} (h1 : Reaches M prog pc s pc' s')
    (h2 : Reaches M prog pc' s' pc'' s'') : Reaches M prog pc s pc'' s'' := by
  induction h1 with
  | refl => exact h2
  | next h _ ih => exact .next h (ih h2)

theorem Reaches.single {M : Machine σ} {prog : List RInstr} {pc : Nat} {s : σ} {pc' : Nat}
    {s' : σ} (h : step M prog pc s = some (.go pc' s')) : Reaches M prog pc s pc' s' :=
  .next h (.refl _ _)

/-- A run from the end of a path is a run from its start with more fuel. -/
theorem run_of_reaches {M : Machine σ} {prog : List RInstr} {pc : Nat} {s : σ} {pc' : Nat}
    {s' : σ} (h : Reaches M prog pc s pc' s') :
    ∀ (fuel : Nat) (r : σ), run M prog fuel pc' s' = some r →
      ∃ fuel', run M prog fuel' pc s = some r := by
  induction h with
  | refl => exact fun fuel r hr => ⟨fuel, hr⟩
  | next hs _ ih =>
    intro fuel r hr
    obtain ⟨f', hf'⟩ := ih fuel r hr
    exact ⟨f' + 1, by rw [run_go _ _ _ _ _ _ _ hs]; exact hf'⟩

/-- The program halts from `pc` in `s'` without a call: a path of `step`s to an index
    holding `ret`. -/
def HaltsNoCall (M : Machine σ) (prog : List RInstr) (pc : Nat) (s s' : σ) : Prop :=
  ∃ pc', Reaches M prog pc s pc' s' ∧ prog[pc']? = some .ret

/-- A call-free halting run is a `run` with enough fuel. -/
theorem run_of_haltsNoCall {M : Machine σ} {prog : List RInstr} {pc : Nat} {s s' : σ}
    (h : HaltsNoCall M prog pc s s') : ∃ fuel, run M prog fuel pc s = some s' := by
  obtain ⟨pc', hr, hret⟩ := h
  exact run_of_reaches hr 1 s' (run_ret M prog 0 pc' s' hret)

/-- The program halts from `pc` in `s''`, running through calls: a continuing `step`,
    a `ret` that ends the run, or a `call t` whose callee runs from `t` to its own `ret`
    on the state after `LprogBytesDecode.callOps`, the caller continuing at the next
    index on the state after `LprogBytesDecode.retOps`. A `ret` ends the innermost run
    of the derivation: in a callee it returns to the caller, at the outermost level it
    halts the program. -/
inductive HaltsC (M : Machine σ) (prog : List RInstr) : Nat → σ → σ → Prop
  | ret {pc : Nat} {s : σ} (h : prog[pc]? = some .ret) : HaltsC M prog pc s s
  | go {pc : Nat} {s : σ} {pc' : Nat} {s' s'' : σ} (h : step M prog pc s = some (.go pc' s'))
      (hr : HaltsC M prog pc' s' s'') : HaltsC M prog pc s s''
  | call {pc t : Nat} {s sc s'' : σ} (h : prog[pc]? = some (.call t))
      (hc : HaltsC M prog t ((LprogBytesDecode.callOps (pc + 1)).foldl M.exec s) sc)
      (hr : HaltsC M prog (pc + 1) (LprogBytesDecode.retOps.foldl M.exec sc) s'') :
      HaltsC M prog pc s s''

/-- The program halts from `pc` in `s'`: the halting run through calls `HaltsC`. -/
abbrev Halts (M : Machine σ) (prog : List RInstr) (pc : Nat) (s s' : σ) : Prop :=
  HaltsC M prog pc s s'

/-- A call-free halting run is a halting run. -/
theorem halts_of_haltsNoCall {M : Machine σ} {prog : List RInstr} {pc : Nat} {s s' : σ}
    (h : HaltsNoCall M prog pc s s') : Halts M prog pc s s' := by
  obtain ⟨pc', hr, hret⟩ := h
  induction hr with
  | refl => exact .ret hret
  | next hs _ ih => exact .go hs (ih hret)

/-- A path of `step`s to an index holding `ret` is a halting run. -/
theorem halts_of_reaches {M : Machine σ} {prog : List RInstr} {pc pc' : Nat} {s s' : σ}
    (hr : Reaches M prog pc s pc' s') (hret : prog[pc']? = some .ret) :
    Halts M prog pc s s' :=
  halts_of_haltsNoCall ⟨pc', hr, hret⟩

/-! ## 3. Segments -/

/-- The element at index `pre.length + k` of `pre ++ ys ++ rest` is `ys[k]`. -/
theorem getElem?_segment (pre ys rest : List RInstr) (k : Nat) (hk : k < ys.length) :
    (pre ++ ys ++ rest)[pre.length + k]? = ys[k]? := by
  rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left hk]

/-- The straight-line fold of `Machine.exec`. -/
def Machine.runBlock (M : Machine σ) (s : σ) : List (JInstr 64) → σ
  | [] => s
  | i :: is => M.runBlock (M.exec s i) is

@[simp] theorem Machine.runBlock_nil (M : Machine σ) (s : σ) : M.runBlock s [] = s := rfl

@[simp] theorem Machine.runBlock_cons (M : Machine σ) (s : σ) (i : JInstr 64)
    (is : List (JInstr 64)) : M.runBlock s (i :: is) = M.runBlock (M.exec s i) is := rfl

theorem Machine.runBlock_append (M : Machine σ) (s : σ) (xs ys : List (JInstr 64)) :
    M.runBlock s (xs ++ ys) = M.runBlock (M.runBlock s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons i is ih => exact ih (M.exec s i)

/-- A segment of `op`s runs as the block fold: from its first index the machine
    reaches the index after it in `M.runBlock s xs`. -/
theorem reaches_ops (M : Machine σ) (pre : List RInstr) (xs : List (JInstr 64))
    (rest : List RInstr) (s : σ) :
    Reaches M (pre ++ xs.map .op ++ rest) pre.length s (pre.length + xs.length)
      (M.runBlock s xs) := by
  induction xs generalizing pre s with
  | nil => rw [List.map_nil, List.append_nil]; exact Reaches.refl _ _
  | cons i is ih =>
    have h := ih (pre ++ [.op i]) (M.exec s i)
    simp only [List.length_append, List.length_cons, List.length_nil, List.append_assoc,
      List.singleton_append, Machine.runBlock_cons] at h ⊢
    refine .next ?_ (by
      rw [show pre.length + (is.length + 1) = pre.length + 1 + is.length by omega]; exact h)
    simp [step]

/-- The condition `NE` reads the zero flag negated. -/
theorem condB_ne (s : JState 64) : s.condB .ne = !s.flagB (·.zf) := rfl

/-- The condition `E` reads the zero flag. -/
theorem condB_e (s : JState 64) : s.condB .e = s.flagB (·.zf) := rfl

theorem condtOfNibble_five : condtOfNibble 5 = some .ne := rfl

theorem condtOfNibble_four : condtOfNibble 4 = some .e := rfl

/-- One pass of a counted loop: the body then `cmp ctr, 0`. -/
def Machine.pass (M : Machine σ) (l : XLoop 64) (s : σ) : σ :=
  M.runBlock s (l.body ++ [l.cmpInstr])

/-- `runXLoop` on a machine: a pass, then fall through on `ZF`, else another pass. -/
def Machine.runXLoop (M : Machine σ) : Nat → σ → XLoop 64 → Option σ
  | 0, _, _ => none
  | fuel + 1, s, l =>
    if (M.view (M.pass l s)).flagB (·.zf) then some (M.pass l s)
    else M.runXLoop fuel (M.pass l s) l

/-- The loop segment `body ++ [cmp ctr, 0] ++ [jne head]` runs as the counted loop:
    with `head` the segment's first index, a terminating `M.runXLoop fuel s l = some s'`
    reaches the index after the segment in `s'`. -/
theorem reaches_xloop (M : Machine σ) (pre : List RInstr) (l : XLoop 64)
    (rest : List RInstr) (fuel : Nat) (s s' : σ) (h : M.runXLoop fuel s l = some s') :
    Reaches M (pre ++ (l.body ++ [l.cmpInstr]).map .op ++ [.jcc 5 pre.length] ++ rest)
      pre.length s (pre.length + l.body.length + 2) s' := by
  induction fuel generalizing s with
  | zero => simp [Machine.runXLoop] at h
  | succ f ih =>
    have hops : Reaches M (pre ++ (l.body ++ [l.cmpInstr]).map .op ++ [.jcc 5 pre.length] ++ rest)
        pre.length s (pre.length + l.body.length + 1) (M.pass l s) := by
      have := reaches_ops M pre (l.body ++ [l.cmpInstr]) ([.jcc 5 pre.length] ++ rest) s
      rw [← List.append_assoc] at this
      simpa [Machine.pass, Nat.add_assoc] using this
    have hj : getElem? (pre ++ (l.body ++ [l.cmpInstr]).map RInstr.op
          ++ [RInstr.jcc 5 pre.length] ++ rest) (pre.length + l.body.length + 1)
        = some (RInstr.jcc 5 pre.length) := by
      simp [List.append_assoc, Nat.add_assoc]
    have hstep : ∀ b, (M.view (M.pass l s)).flagB (·.zf) = b →
        step M (pre ++ (l.body ++ [l.cmpInstr]).map .op ++ [.jcc 5 pre.length] ++ rest)
          (pre.length + l.body.length + 1) (M.pass l s)
        = some (if b then .go (pre.length + l.body.length + 1 + 1) (M.pass l s)
            else .go pre.length (M.pass l s)) := by
      intro b hb
      simp only [step, hj, condtOfNibble_five, Option.map_some, condB_ne, hb]
      cases b <;> rfl
    simp only [Machine.runXLoop] at h
    split at h
    · rename_i hz
      simp only [Option.some.injEq] at h
      subst h
      exact hops.trans (.single (by rw [hstep true hz, if_pos rfl]))
    · rename_i hz
      exact hops.trans (.next (by rw [hstep false (by simpa using hz), if_neg Bool.false_ne_true])
        (ih _ h))

/-! ## 4. The name-keyed machine -/

/-- The name-keyed machine: `evalInstr` on `JState 64`. -/
def jMachine : Machine (JState 64) := ⟨evalInstr, id⟩

theorem jMachine_runBlock (s : JState 64) (xs : List (JInstr 64)) :
    jMachine.runBlock s xs = runBlock s xs := by
  induction xs generalizing s with
  | nil => rfl
  | cons i is ih => exact ih (evalInstr s i)

theorem jMachine_view (s : JState 64) : jMachine.view s = s := rfl

theorem jMachine_pass (l : XLoop 64) (s : JState 64) : jMachine.pass l s = l.pass s := by
  simp [Machine.pass, XLoop.pass, jMachine_runBlock]

theorem jMachine_runXLoop (fuel : Nat) (s : JState 64) (l : XLoop 64) :
    jMachine.runXLoop fuel s l = runXLoop fuel s l := by
  induction fuel generalizing s with
  | zero => rfl
  | succ f ih => rw [Machine.runXLoop, runXLoop, jMachine_pass, jMachine_view, ih]

end CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
