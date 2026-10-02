/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
public import CatCryptCore.Tactics.KatGuard
public import Std.Data.HashMap
public import Std.Data.HashSet

/-!
# The control-flow graph of an `Lcmd` body

The basic blocks of a linear body and the edges between them, with the theorem that a
halting run of a labelled semantics over the body is a path in the graph, and its
converse.

Leaders are index `0`, the index of every `Llabel`, and the index after every `Lgoto`,
`Lcond` and `Lret`. A block ends in one of four terminators (`Term`): it falls through to
the next block (or out of the body, which halts), jumps with `Lgoto`, branches with
`Lcond` (the label's block or the fall-through), or ends in `Lret`. A jump to label `l`
targets the block starting at `findLabel l`, the first `Llabel _ l`; the semantics sets the
pc one past that label, so a jump enters its target block at the instruction after the
label, and a fall-through enters at the block start.

`cfgOf` builds the graph with arrays and a label table, then validates it with `wf`,
a check that states only what the path theorem uses: contiguous non-empty blocks covering
the body, no terminator inside a block, and each block's terminator matching its last
instruction with jump targets resolved by `findLabel`. It rejects a jump to an absent
label, a duplicated label, and a body containing `Lcall`, `Lsyscall`, `Ligoto` or
`LstoreLabel`.

The semantics is a parameter: `LMachine` bundles a pc, a step, a fuel iterator and an
invariant, and `LMachine.Sound` the facts the path theorem needs (a step from pc `p`
lands at a pc allowed by `NextPc` for the instruction at `p`; the iterator halts exactly
when the pc leaves the body). `Lret` has no successor pc: a step at `Lret` fails, so a
halting run leaves the body only by falling off its end, at pc equal to its length.

## Main definitions

* `Term`, `Block`, `CFG`, `CFG.succs`, `CFG.predsOf`, `CFG.blockOfPc`, `CFG.labelOf`.
* `cfgOf : List LinstrR → Option CFG` and `cfgOfLcmd : Lcmd → Option CFG`.
* `NextPc`, `LMachine`, `LMachine.Sound`, `LMachine.steps`.
* `BlockPath M wl G b s t`: from state `s` inside block `b`, the run reaches `t` along
  a path of blocks, each run for the instructions up to its end.
* `memLMachine P`: the memref loop semantics `lsemFuelMemL` as an `LMachine`.

## Main results

* `blockPath_of_run`: a halting run from a state inside a block is a `BlockPath`.
* `run_of_blockPath`: a `BlockPath` is a halting run.
* `memLMachine_sound`: the memref loop semantics satisfies `LMachine.Sound`.
* `lsemL_path`, `path_lsemL`: the two directions for `lsemFuelMemL` on a singleton
  program.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled (findLabel findLabel_sound isLabel)

/-! ## 1. Instruction classes -/

/-- An instruction that ends a block: `Lgoto`, `Lcond` or `Lret`. -/
def isTermR : LinstrR → Bool
  | .Lgoto _ => true
  | .Lcond _ _ => true
  | .Lret => true
  | _ => false

/-- A label declaration. -/
def isLabelR : LinstrR → Bool
  | .Llabel _ _ => true
  | _ => false

/-- An instruction `cfgOf` rejects: a call, a system call, an indirect jump, or a label
    store. -/
def isBarredR : LinstrR → Bool
  | .Lcall _ _ => true
  | .Lsyscall _ => true
  | .Ligoto _ => true
  | .LstoreLabel _ _ => true
  | _ => false

/-! ## 2. Blocks and the graph -/

/-- The terminator of a block. `next = none` in `fall` and `cond` means that falling
    through leaves the body. -/
inductive Term where
  /-- Fall through to `next`, or leave the body. -/
  | fall (next : Option Nat)
  /-- `Lgoto` to block `target`. -/
  | goto (target : Nat)
  /-- `Lcond` to block `target`, else fall through to `next` or leave the body. -/
  | cond (target : Nat) (next : Option Nat)
  /-- `Lret`. -/
  | ret
  deriving DecidableEq, Repr, Inhabited

namespace Term

/-- The successor blocks of a terminator. -/
def succs : Term → List Nat
  | .fall nx => nx.toList
  | .goto t => [t]
  | .cond t nx => t :: nx.toList
  | .ret => []

/-- A terminator whose fall-through leaves the body. -/
def halts : Term → Bool
  | .fall none => true
  | .cond _ none => true
  | _ => false

end Term

/-- A basic block: the instructions at indices `start ≤ pc < stop` and its terminator. -/
structure Block where
  /-- The index of the first instruction (a leader). -/
  start : Nat
  /-- One past the index of the last instruction. -/
  stop : Nat
  /-- The terminator. -/
  term : Term
  deriving DecidableEq, Repr, Inhabited

/-- The control-flow graph of a body: its blocks in body order, the block of every
    instruction index, and the predecessor lists. -/
structure CFG where
  /-- The blocks in body order. -/
  blocks : Array Block
  /-- `blockOf[pc]` is the block containing index `pc`. -/
  blockOf : Array Nat
  /-- `preds[b]` lists the blocks with an edge to `b`. -/
  preds : Array (List Nat)
  deriving Repr

namespace CFG

/-- Block `b` (the default block out of range). -/
def blk (G : CFG) (b : Nat) : Block := G.blocks.getD b default

/-- The successors of block `b`. -/
def succs (G : CFG) (b : Nat) : List Nat := (G.blk b).term.succs

/-- The predecessors of block `b`. -/
def predsOf (G : CFG) (b : Nat) : List Nat := G.preds.getD b []

/-- The block containing instruction index `pc`. -/
def blockOfPc (G : CFG) (pc : Nat) : Option Nat := G.blockOf[pc]?

/-- The fall-through block of block `k`. -/
def next (G : CFG) (k : Nat) : Option Nat :=
  if k + 1 < G.blocks.size then some (k + 1) else none

/-- The index where block `k` must end: the next block's start, or the body length `n`. -/
def nextStart (G : CFG) (n k : Nat) : Nat :=
  match G.next k with
  | some k' => (G.blk k').start
  | none => n

/-- The number of edges. -/
def numEdges (G : CFG) : Nat :=
  (List.range G.blocks.size).foldl (fun a b => a + (G.succs b).length) 0

/-- The block a jump to label `l` targets in body `wl`. -/
def labelOf (G : CFG) (wl : List LinstrR) (l : LLabel) : Option Nat :=
  (findLabel l wl).bind G.blockOfPc

/-- The instruction indices at which control enters block `b`: its start (by
    fall-through), and the index after its first instruction when that is a label (by a
    jump). -/
def Entry (G : CFG) (wl : List LinstrR) (b pc : Nat) : Prop :=
  pc = (G.blk b).start ∨
    (pc = (G.blk b).start + 1 ∧ (wl[(G.blk b).start]?.any isLabelR) = true)

end CFG

/-! ## 3. Construction -/

/-- Index `pc` starts a block: it is `0`, a label, or follows a terminator. -/
def isLeader (w : Array LinstrR) (pc : Nat) : Bool :=
  pc == 0 || (w[pc]?.any isLabelR) ||
    (match pc with
     | 0 => false
     | p + 1 => w[p]?.any isTermR)

/-- The leaders of a body in increasing order. -/
def leaderStarts (w : Array LinstrR) : Array Nat := Id.run do
  let mut acc : Array Nat := #[]
  for pc in [0:w.size] do
    if isLeader w pc then acc := acc.push pc
  return acc

/-- The block index of each of the `n` instruction indices, given the block starts. -/
def blockIndex (n : Nat) (starts : Array Nat) : Array Nat := Id.run do
  let mut out : Array Nat := Array.mkEmpty n
  let mut b := 0
  for pc in [0:n] do
    if b + 1 < starts.size && starts[b + 1]! == pc then b := b + 1
    out := out.push b
  return out

/-- The index of the first declaration of each label. -/
def firstLabelPcs (w : Array LinstrR) : Std.HashMap LLabel Nat := Id.run do
  let mut m : Std.HashMap LLabel Nat := {}
  let mut pc := 0
  for i in w do
    match i with
    | .Llabel _ l => if !m.contains l then m := m.insert l pc
    | _ => pure ()
    pc := pc + 1
  return m

/-- Some label is declared twice. -/
def hasDupLabel (w : Array LinstrR) : Bool := Id.run do
  let mut seen : Std.HashSet LLabel := {}
  for i in w do
    match i with
    | .Llabel _ l =>
        if seen.contains l then return true
        seen := seen.insert l
    | _ => pure ()
  return false

/-- The graph of a body before validation; `none` when a jump names an absent label. -/
def build (w : Array LinstrR) : Option CFG := do
  let starts := leaderStarts w
  let nb := starts.size
  let bOf := blockIndex w.size starts
  let lbl := firstLabelPcs w
  let target : LLabel → Option Nat := fun l => lbl[l]?.bind (fun pc => bOf[pc]?)
  let mut blocks : Array Block := Array.mkEmpty nb
  for k in [0:nb] do
    let start := starts[k]!
    let stop := if k + 1 < nb then starts[k + 1]! else w.size
    let nx := if k + 1 < nb then some (k + 1) else none
    let term ← match w[stop - 1]? with
      | some (.Lgoto (_, l)) => (target l).map Term.goto
      | some (.Lcond _ l) => (target l).map (fun t => Term.cond t nx)
      | some .Lret => some Term.ret
      | _ => some (Term.fall nx)
    blocks := blocks.push { start, stop, term }
  let mut preds : Array (List Nat) := Array.replicate nb []
  for k in [0:nb] do
    for s in (blocks.getD k default).term.succs do
      preds := preds.modify s (fun l => l ++ [k])
  return { blocks, blockOf := bOf, preds }

/-! ## 4. Validation -/

/-- Terminator `T` of block `k` matches the block's last instruction. -/
def termOk (wl : List LinstrR) (G : CFG) (k : Nat) : Term → Option LinstrR → Bool
  | .goto t, some (.Lgoto (_, l)) =>
      decide (t < G.blocks.size) && decide (findLabel l wl = some (G.blk t).start)
  | .cond t nx, some (.Lcond _ l) =>
      decide (t < G.blocks.size) && decide (findLabel l wl = some (G.blk t).start) &&
        decide (nx = G.next k)
  | .ret, some .Lret => true
  | .fall nx, some i => !isTermR i && decide (nx = G.next k)
  | _, _ => false

/-- Block `k` is non-empty, ends where the next block starts (or at the body end), has
    no terminator before its last instruction, and its terminator matches that
    instruction. -/
def blockOk (wl : List LinstrR) (w : Array LinstrR) (G : CFG) (k : Nat) : Bool :=
  let B := G.blk k
  decide (B.start < B.stop) && decide (B.stop ≤ w.size) &&
    decide (B.stop = G.nextStart w.size k) &&
    (List.range' B.start (B.stop - 1 - B.start)).all (fun pc => !(w[pc]?.any isTermR)) &&
    termOk wl G k B.term w[B.stop - 1]?

/-- `blockOf` sends every index to a block containing it. -/
def blockOfOk (w : Array LinstrR) (G : CFG) : Bool :=
  decide (G.blockOf.size = w.size) &&
    (List.range w.size).all fun pc =>
      let b := G.blockOf.getD pc 0
      decide (b < G.blocks.size) && decide ((G.blk b).start ≤ pc) &&
        decide (pc < (G.blk b).stop)

/-- The validation of a graph against body `wl` (with `w = wl.toArray`). -/
def wf (wl : List LinstrR) (w : Array LinstrR) (G : CFG) : Bool :=
  (if G.blocks.size = 0 then decide (w.size = 0) else decide ((G.blk 0).start = 0)) &&
    (List.range G.blocks.size).all (blockOk wl w G) &&
    blockOfOk w G && !(w.any isBarredR) && !hasDupLabel w

/-- The control-flow graph of a body, or `none` when the body jumps to an absent label,
    declares a label twice, or contains `Lcall`, `Lsyscall`, `Ligoto` or
    `LstoreLabel`. -/
def cfgOf (wl : List LinstrR) : Option CFG :=
  let w := wl.toArray
  match build w with
  | some G => if wf wl w G then some G else none
  | none => none

/-- `cfgOf` on the instructions of an `Lcmd`. -/
def cfgOfLcmd (c : Lcmd) : Option CFG := cfgOf (c.map Linstr.li_i)

/-! ## 5. What validation gives -/

theorem cfgOf_wf {wl : List LinstrR} {G : CFG} (h : cfgOf wl = some G) :
    wf wl wl.toArray G = true := by
  unfold cfgOf at h
  dsimp only at h
  split at h
  · split at h
    · cases h; assumption
    · cases h
  · cases h

/-- The per-block facts `wf` states. -/
structure BlockFacts (wl : List LinstrR) (G : CFG) (k : Nat) : Prop where
  lt : (G.blk k).start < (G.blk k).stop
  le : (G.blk k).stop ≤ wl.length
  stop_eq : (G.blk k).stop = G.nextStart wl.length k
  inner : ∀ pc i, (G.blk k).start ≤ pc → pc + 1 < (G.blk k).stop → wl[pc]? = some i →
    isTermR i = false
  term : termOk wl G k (G.blk k).term wl[(G.blk k).stop - 1]? = true

theorem blockFacts {wl : List LinstrR} {G : CFG} (h : cfgOf wl = some G) {k : Nat}
    (hk : k < G.blocks.size) : BlockFacts wl G k := by
  have hw := cfgOf_wf h
  simp only [wf, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hw
  have hb := hw.1.1.1.2 k hk
  simp only [blockOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range'_1, List.getElem?_toArray, List.size_toArray] at hb
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hb
  refine ⟨h1, h2, h3, ?_, h5⟩
  intro pc i hs hl hi
  have := h4 pc ⟨hs, by omega⟩
  simpa [hi] using this

theorem cfgOf_start_zero {wl : List LinstrR} {G : CFG} (h : cfgOf wl = some G)
    (hne : wl ≠ []) : 0 < G.blocks.size ∧ (G.blk 0).start = 0 := by
  have hw := cfgOf_wf h
  simp only [wf, Bool.and_eq_true] at hw
  have h0 := hw.1.1.1.1
  by_cases hz : G.blocks.size = 0
  · rw [if_pos hz] at h0
    simp only [decide_eq_true_eq, List.size_toArray, List.length_eq_zero_iff] at h0
    exact absurd h0 hne
  · rw [if_neg hz] at h0
    exact ⟨Nat.pos_of_ne_zero hz, by simpa using h0⟩

/-- The terminator check, as a case split on the terminator. -/
theorem termOk_spec {wl : List LinstrR} {G : CFG} {k : Nat} {T : Term} {i : LinstrR}
    (h : termOk wl G k T (some i) = true) :
    (∃ nx, T = .fall nx ∧ isTermR i = false ∧ nx = G.next k) ∨
    (∃ t x l, T = .goto t ∧ i = .Lgoto (x, l) ∧ t < G.blocks.size ∧
      findLabel l wl = some (G.blk t).start) ∨
    (∃ t nx c l, T = .cond t nx ∧ i = .Lcond c l ∧ t < G.blocks.size ∧
      findLabel l wl = some (G.blk t).start ∧ nx = G.next k) ∨
    (T = .ret ∧ i = .Lret) := by
  cases T <;> cases i
  case goto.Lgoto t tg =>
    obtain ⟨x, l⟩ := tg
    simp_all [termOk]
  all_goals simp_all [termOk, isTermR]

/-! ## 6. Labelled machines -/

/-- The pcs a successful step of instruction `i` at pc `pc` may reach: a jump lands one
    past its label's first declaration, `Lcond` also falls through, `Lret` has no
    successor, and every other instruction advances the pc by one. -/
def NextPc (wl : List LinstrR) : LinstrR → Nat → Nat → Prop
  | .Lgoto (_, l), _, pc' => ∃ q, findLabel l wl = some q ∧ pc' = q + 1
  | .Lcond _ l, pc, pc' => pc' = pc + 1 ∨ ∃ q, findLabel l wl = some q ∧ pc' = q + 1
  | .Lret, _, _ => False
  | .Lopn _ _ _, pc, pc' => pc' = pc + 1
  | .Lsyscall _, pc, pc' => pc' = pc + 1
  | .Lcall _ _, pc, pc' => pc' = pc + 1
  | .Lalign, pc, pc' => pc' = pc + 1
  | .Llabel _ _, pc, pc' => pc' = pc + 1
  | .Ligoto _, pc, pc' => pc' = pc + 1
  | .LstoreLabel _ _, pc, pc' => pc' = pc + 1

theorem nextPc_plain {wl : List LinstrR} {i : LinstrR} {pc pc' : Nat}
    (hi : isTermR i = false) (h : NextPc wl i pc pc') : pc' = pc + 1 := by
  cases i <;> simp_all [isTermR, NextPc]

/-- A labelled semantics over a body: a pc, a step, a fuel iterator and an invariant
    (typically: the current function is the body's). -/
structure LMachine (σ : Type) where
  /-- The program counter. -/
  pc : σ → Nat
  /-- One step. -/
  step : σ → Option σ
  /-- The fuel iterator. -/
  run : Nat → σ → Option σ
  /-- The invariant under which the facts of `Sound` hold. -/
  inv : σ → Prop

/-- The facts about a labelled machine over body `wl` that the path theorem uses. -/
structure LMachine.Sound {σ : Type} (M : LMachine σ) (wl : List LinstrR) : Prop where
  step_inv : ∀ s s', M.inv s → M.step s = some s' → M.inv s'
  step_lt : ∀ s s', M.inv s → M.step s = some s' → M.pc s < wl.length
  step_next : ∀ s s' i, M.inv s → M.step s = some s' → wl[M.pc s]? = some i →
    NextPc wl i (M.pc s) (M.pc s')
  run_zero : ∀ s, M.inv s → M.pc s < wl.length → M.run 0 s = none
  run_succ : ∀ f s, M.inv s → M.pc s < wl.length → M.run (f + 1) s = (M.step s).bind (M.run f)
  run_halt : ∀ f s, M.inv s → wl.length ≤ M.pc s → M.run f s = some s

/-- `n` steps. -/
def LMachine.steps {σ : Type} (M : LMachine σ) : Nat → σ → Option σ
  | 0, s => some s
  | n + 1, s =>
      match M.step s with
      | some s' => M.steps n s'
      | none => none

section Machine

variable {σ : Type} {M : LMachine σ} {wl : List LinstrR}

theorem LMachine.steps_succ_of_step {s s1 : σ} (n : Nat) (h : M.step s = some s1) :
    M.steps (n + 1) s = M.steps n s1 := by
  simp [LMachine.steps, h]

theorem LMachine.steps_inv (hM : M.Sound wl) :
    ∀ (n : Nat) (s u : σ), M.inv s → M.steps n s = some u → M.inv u := by
  intro n
  induction n with
  | zero => intro s u hs h; simp [LMachine.steps] at h; exact h ▸ hs
  | succ n ih =>
      intro s u hs h
      unfold LMachine.steps at h
      split at h
      · rename_i s' hs'
        exact ih s' u (hM.step_inv s s' hs hs') h
      · cases h

theorem LMachine.steps_run (hM : M.Sound wl) :
    ∀ (n : Nat) (s u : σ), M.inv s → M.steps n s = some u →
      ∀ f, M.run (n + f) s = M.run f u := by
  intro n
  induction n with
  | zero => intro s u _ h f; simp [LMachine.steps] at h; simp [h]
  | succ n ih =>
      intro s u hs h f
      unfold LMachine.steps at h
      split at h
      · rename_i s' hs'
        rw [show n + 1 + f = (n + f) + 1 by omega,
          hM.run_succ _ s hs (hM.step_lt s s' hs hs'), hs', Option.bind_some]
        exact ih s' u (hM.step_inv s s' hs hs') h f
      · cases h

end Machine

/-! ## 7. Paths of blocks -/

/-- From state `s` inside block `b`, the run reaches the halted state `t` along a path of
    blocks: each block runs for the instructions from the current pc to its end, and
    the state reached either enters a successor block (at an `Entry` index) or has left
    the body through a halting terminator. -/
inductive BlockPath {σ : Type} (M : LMachine σ) (wl : List LinstrR) (G : CFG) :
    Nat → σ → σ → Prop
  /-- The block runs to its end and control leaves the body. -/
  | halt {b : Nat} {s u : σ} :
      M.steps ((G.blk b).stop - M.pc s) s = some u → (G.blk b).term.halts = true →
      M.pc u = wl.length → BlockPath M wl G b s u
  /-- The block runs to its end and control enters successor `b'`. -/
  | edge {b b' : Nat} {s u t : σ} :
      M.steps ((G.blk b).stop - M.pc s) s = some u → b' ∈ G.succs b →
      G.Entry wl b' (M.pc u) → BlockPath M wl G b' u t → BlockPath M wl G b s t

section Path

variable {σ : Type} {M : LMachine σ} {wl : List LinstrR} {G : CFG}

theorem BlockPath.prepend {b : Nat} {s s1 t : σ} (hstep : M.step s = some s1)
    (hpc : M.pc s1 = M.pc s + 1) (hlt : M.pc s < (G.blk b).stop)
    (h : BlockPath M wl G b s1 t) : BlockPath M wl G b s t := by
  have hk : (G.blk b).stop - M.pc s = ((G.blk b).stop - M.pc s1) + 1 := by omega
  cases h with
  | halt hs hh hu =>
      exact .halt (by rw [hk, LMachine.steps_succ_of_step _ hstep]; exact hs) hh hu
  | edge hs hb he hp =>
      exact .edge (by rw [hk, LMachine.steps_succ_of_step _ hstep]; exact hs) hb he hp

/-- **A `BlockPath` is a halting run.** -/
theorem run_of_blockPath (hM : M.Sound wl) {b : Nat} {s t : σ}
    (h : BlockPath M wl G b s t) (hs : M.inv s) : ∃ f, M.run f s = some t := by
  induction h with
  | @halt b s u hst _ hu =>
      refine ⟨(G.blk b).stop - M.pc s + 0, ?_⟩
      rw [LMachine.steps_run hM _ s u hs hst 0]
      exact hM.run_halt 0 u (LMachine.steps_inv hM _ s u hs hst) (by omega)
  | @edge b b' s u t hst _ _ _ ih =>
      obtain ⟨f, hf⟩ := ih (LMachine.steps_inv hM _ s u hs hst)
      exact ⟨_, (LMachine.steps_run hM _ s u hs hst f).trans hf⟩

/-- The induction hypothesis of `blockPath_of_run` at fuel `f`. -/
def PathIH (M : LMachine σ) (wl : List LinstrR) (G : CFG) (f : Nat) (t : σ) : Prop :=
  ∀ b s, M.inv s → b < G.blocks.size → (G.blk b).start ≤ M.pc s →
    M.pc s < (G.blk b).stop → M.run f s = some t → BlockPath M wl G b s t

/-- Control at the end of block `k` falls through: to the next block, or out of the
    body. -/
theorem fall_cont (hM : M.Sound wl) (hG : cfgOf wl = some G) {f : Nat} {t : σ}
    (ih : PathIH M wl G f t) {k : Nat} {u : σ} (hk : k < G.blocks.size) (hinv : M.inv u)
    (hpc : M.pc u = (G.blk k).stop) (hrun : M.run f u = some t) :
    (∃ k', G.next k = some k' ∧ G.Entry wl k' (M.pc u) ∧ BlockPath M wl G k' u t) ∨
      (G.next k = none ∧ M.pc u = wl.length ∧ t = u) := by
  have F := blockFacts hG hk
  have hse := F.stop_eq
  by_cases hn : k + 1 < G.blocks.size
  · have hnx : G.next k = some (k + 1) := by simp [CFG.next, hn]
    rw [CFG.nextStart, hnx] at hse
    dsimp only at hse
    have F' := blockFacts hG hn
    refine Or.inl ⟨k + 1, hnx, Or.inl (by omega), ?_⟩
    exact ih (k + 1) u hinv hn (by omega) (by have := F'.lt; omega) hrun
  · have hnx : G.next k = none := by simp [CFG.next, hn]
    rw [CFG.nextStart, hnx] at hse
    dsimp only at hse
    have hlen : M.pc u = wl.length := by omega
    rw [hM.run_halt f u hinv (by omega)] at hrun
    exact Or.inr ⟨hnx, hlen, (Option.some.inj hrun).symm⟩

/-- A jump lands one past the label that starts block `k'`. -/
theorem jump_cont (hM : M.Sound wl) (hG : cfgOf wl = some G) {f : Nat} {t : σ}
    (ih : PathIH M wl G f t) {k' : Nat} {l : LLabel} {u : σ} (hk : k' < G.blocks.size)
    (hl : findLabel l wl = some (G.blk k').start) (hinv : M.inv u)
    (hpc : M.pc u = (G.blk k').start + 1) (hrun : M.run f u = some t) :
    G.Entry wl k' (M.pc u) ∧ BlockPath M wl G k' u t := by
  have F := blockFacts hG hk
  obtain ⟨j, hj, hjl⟩ := findLabel_sound l wl _ hl
  have hjlab : isLabelR j = true := by
    cases j <;> simp_all [isLabel, isLabelR]
  refine ⟨Or.inr ⟨hpc, by simp [hj, hjlab]⟩, ?_⟩
  by_cases hlt : M.pc u < (G.blk k').stop
  · exact ih k' u hinv hk (by omega) hlt hrun
  · have hstop : (G.blk k').stop = (G.blk k').start + 1 := by have := F.lt; omega
    have hterm := F.term
    rw [show (G.blk k').stop - 1 = (G.blk k').start by omega, hj] at hterm
    have hzero : M.steps ((G.blk k').stop - M.pc u) u = some u := by
      rw [show (G.blk k').stop - M.pc u = 0 by omega]; rfl
    rcases termOk_spec hterm with ⟨nx, hT, _, hnx⟩ | ⟨_, _, _, _, hi, _⟩ |
      ⟨_, _, _, _, _, hi, _⟩ | ⟨_, hi⟩
    · rcases fall_cont hM hG ih hk hinv (by omega) hrun with
        ⟨k'', hk'', he, hp⟩ | ⟨hnone, hlen, rfl⟩
      · exact .edge hzero (by simp [CFG.succs, hT, Term.succs, hnx, hk'']) he hp
      · exact .halt hzero (by simp [hT, Term.halts, hnx, hnone]) hlen
    all_goals (subst hi; simp [isLabelR] at hjlab)

/-- **A halting run from a state inside a block is a path of blocks.** -/
theorem blockPath_of_run (hM : M.Sound wl) (hG : cfgOf wl = some G) (t : σ) :
    ∀ (fuel b : Nat) (s : σ), M.inv s → b < G.blocks.size → (G.blk b).start ≤ M.pc s →
      M.pc s < (G.blk b).stop → M.run fuel s = some t → BlockPath M wl G b s t := by
  intro fuel
  induction fuel with
  | zero =>
      intro b s hinv hb _ h2 hrun
      have F := blockFacts hG hb
      rw [hM.run_zero s hinv (by have := F.le; omega)] at hrun
      cases hrun
  | succ f ih =>
      intro b s hinv hb h1 h2 hrun
      have F := blockFacts hG hb
      have hlt : M.pc s < wl.length := by have := F.le; omega
      rw [hM.run_succ f s hinv hlt] at hrun
      cases hs : M.step s with
      | none => rw [hs] at hrun; cases hrun
      | some s1 =>
        rw [hs, Option.bind_some] at hrun
        have hinv1 := hM.step_inv s s1 hinv hs
        have hi : wl[M.pc s]? = some wl[M.pc s] := List.getElem?_eq_getElem hlt
        have hnext := hM.step_next s s1 _ hinv hs hi
        by_cases hmid : M.pc s + 1 < (G.blk b).stop
        · have hpc1 := nextPc_plain (F.inner (M.pc s) _ h1 hmid hi) hnext
          exact BlockPath.prepend hs hpc1 h2 (ih b s1 hinv1 hb (by omega) (by omega) hrun)
        · have hlast : (G.blk b).stop - 1 = M.pc s := by omega
          have hsteps : M.steps ((G.blk b).stop - M.pc s) s = some s1 := by
            rw [show (G.blk b).stop - M.pc s = 0 + 1 by omega,
              LMachine.steps_succ_of_step _ hs]
            rfl
          have hterm := F.term
          rw [hlast, hi] at hterm
          rcases termOk_spec hterm with ⟨nx, hT, hnt, hnx⟩ |
              ⟨t', x, l, hT, hi', ht', hl⟩ | ⟨t', nx, c, l, hT, hi', ht', hl, hnx⟩ | ⟨_, hi'⟩
          · have hpc1 := nextPc_plain hnt hnext
            rcases fall_cont hM hG ih hb hinv1 (by omega) hrun with
              ⟨k', hk', he, hp⟩ | ⟨hnone, hlen, rfl⟩
            · exact .edge hsteps (by simp [CFG.succs, hT, Term.succs, hnx, hk']) he hp
            · exact .halt hsteps (by simp [hT, Term.halts, hnx, hnone]) hlen
          · rw [hi'] at hnext
            obtain ⟨q, hq, hpc1⟩ := hnext
            rw [hl] at hq
            cases hq
            obtain ⟨he, hp⟩ := jump_cont hM hG ih ht' hl hinv1 hpc1 hrun
            exact .edge hsteps (by simp [CFG.succs, hT, Term.succs]) he hp
          · rw [hi'] at hnext
            rcases hnext with hpc1 | ⟨q, hq, hpc1⟩
            · rcases fall_cont hM hG ih hb hinv1 (by omega) hrun with
                ⟨k', hk', he, hp⟩ | ⟨hnone, hlen, rfl⟩
              · exact .edge hsteps (by simp [CFG.succs, hT, Term.succs, hnx, hk']) he hp
              · exact .halt hsteps (by simp [hT, Term.halts, hnx, hnone]) hlen
            · rw [hl] at hq
              cases hq
              obtain ⟨he, hp⟩ := jump_cont hM hG ih ht' hl hinv1 hpc1 hrun
              exact .edge hsteps (by simp [CFG.succs, hT, Term.succs]) he hp
          · rw [hi'] at hnext
            exact hnext.elim

end Path

/-! ## 8. The memref loop semantics as a labelled machine -/

/-- A jump sets the pc one past the label's first declaration and keeps the function. -/
theorem evalJumpMem_spec (P : LprogM) (l : LLabel) (s p : LstatePM)
    (h : evalJumpMem P l s = some p) :
    p.lfn = s.lfn ∧ ∃ q, findLabel l (P.body.map Prod.fst) = some q ∧ p.base.lpc = q + 1 := by
  unfold evalJumpMem findLabelMem at h
  split at h
  · rename_i q hq
    cases h
    exact ⟨rfl, q, hq, rfl⟩
  · cases h

/-- `Lret` takes no step in the memref semantics. -/
theorem lsemStepMem_ret (tag : MemTag) (b : LstateM) : lsemStepMem (.Lret, tag) b = none := by
  cases tag <;> rfl

/-- A successful step of the memref loop semantics keeps the function and reaches a pc
    allowed by `NextPc`. -/
theorem evalInstrPMemL_next (P : LprogM) (i : LinstrRM) (s p : LstatePM)
    (h : evalInstrPMemL P i s = some p) :
    p.lfn = s.lfn ∧ NextPc (P.body.map Prod.fst) i.1 s.base.lpc p.base.lpc := by
  obtain ⟨ir, tag⟩ := i
  have hgen : ∀ ir' : LinstrR, (lsemStepMem (ir', tag) s.base).map
      (fun b => ({ s with base := b } : LstatePM)) = some p →
      p.lfn = s.lfn ∧ p.base.lpc = s.base.lpc + 1 := by
    intro ir' h'
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h'
    exact ⟨rfl, lsemStepMem_lpc_succ _ _ _ hb⟩
  unfold evalInstrPMemL at h
  cases ir with
  | Lgoto target =>
      obtain ⟨fn, l⟩ := target
      simp only at h
      split at h
      · exact evalJumpMem_spec P l s p h
      · cases h
  | Lcond c l =>
      simp only at h
      split at h
      · obtain ⟨h1, h2⟩ := evalJumpMem_spec P l s p h
        exact ⟨h1, Or.inr h2⟩
      · cases h
        exact ⟨rfl, Or.inl (by simp)⟩
  | Llabel k l =>
      simp only at h
      cases h
      exact ⟨rfl, by simp [NextPc]⟩
  | Lret =>
      simp only [lsemStepMem_ret] at h
      cases h
  | Lopn d o a => exact hgen _ h
  | Lsyscall n => exact hgen _ h
  | Lcall r t => exact hgen _ h
  | Lalign => exact hgen _ h
  | Ligoto t => exact hgen _ h
  | LstoreLabel d l => exact hgen _ h

/-- The memref loop semantics of program `P` as a labelled machine. -/
def memLMachine (P : LprogM) : LMachine LstatePM where
  pc s := s.base.lpc
  step := lsemStepPMemL P
  run := lsemFuelMemL P
  inv s := s.lfn = P.lfn

theorem findInstrMem_of_lt (P : LprogM) (s : LstatePM) (hfn : s.lfn = P.lfn)
    (hlt : s.base.lpc < P.body.length) :
    findInstrMem P s = some P.body[s.base.lpc] := by
  unfold findInstrMem
  rw [if_pos hfn]
  exact List.getElem?_eq_getElem hlt

theorem findInstrMem_of_ge (P : LprogM) (s : LstatePM) (hge : P.body.length ≤ s.base.lpc) :
    findInstrMem P s = none := by
  unfold findInstrMem
  split
  · exact List.getElem?_eq_none hge
  · rfl

/-- **The memref loop semantics satisfies `LMachine.Sound`.** -/
theorem memLMachine_sound (P : LprogM) : (memLMachine P).Sound (P.body.map Prod.fst) where
  step_inv s s' hs h := by
    simp only [memLMachine, lsemStepPMemL] at h hs ⊢
    split at h
    · rw [(evalInstrPMemL_next P _ s s' h).1, hs]
    · cases h
  step_lt s s' hs h := by
    simp only [memLMachine, lsemStepPMemL, List.length_map] at h hs ⊢
    split at h
    · rename_i i hi
      unfold findInstrMem at hi
      rw [if_pos hs] at hi
      exact (List.getElem?_eq_some_iff.mp hi).1
    · cases h
  step_next s s' i hs h hi := by
    simp only [memLMachine, lsemStepPMemL] at h hs hi ⊢
    split at h
    · rename_i j hj
      unfold findInstrMem at hj
      rw [if_pos hs] at hj
      rw [List.getElem?_map, hj] at hi
      cases hi
      exact (evalInstrPMemL_next P j s s' h).2
    · cases h
  run_zero s hs hlt := by
    simp only [memLMachine, List.length_map] at hs hlt ⊢
    rw [lsemFuelMemL, findInstrMem_of_lt P s hs hlt]
  run_succ f s hs hlt := by
    simp only [memLMachine, List.length_map] at hs hlt ⊢
    rw [lsemFuelMemL, lsemStepPMemL, findInstrMem_of_lt P s hs hlt]
    dsimp only
    cases evalInstrPMemL P _ s <;> rfl
  run_halt f s _ hge := by
    simp only [memLMachine, List.length_map] at hge ⊢
    exact lsemFuelMemL_halt P f s (findInstrMem_of_ge P s hge)

/-- **A halting `lsemFuelMemL` run of a singleton program is a path of blocks.** -/
theorem lsemL_path {fn : String} {body : List LinstrRM} {G : CFG}
    (hG : cfgOf (body.map Prod.fst) = some G) (fuel b : Nat) (s t : LstatePM)
    (hfn : s.lfn = fn) (hb : b < G.blocks.size) (h1 : (G.blk b).start ≤ s.base.lpc)
    (h2 : s.base.lpc < (G.blk b).stop)
    (hrun : lsemFuelMemL (singletonProgM fn body) fuel s = some t) :
    BlockPath (memLMachine (singletonProgM fn body)) (body.map Prod.fst) G b s t :=
  blockPath_of_run (memLMachine_sound (singletonProgM fn body)) hG t fuel b s hfn hb h1 h2
    hrun

/-- **A path of blocks is a halting `lsemFuelMemL` run.** -/
theorem path_lsemL {fn : String} {body : List LinstrRM} {G : CFG} {b : Nat}
    {s t : LstatePM} (hfn : s.lfn = fn)
    (h : BlockPath (memLMachine (singletonProgM fn body)) (body.map Prod.fst) G b s t) :
    ∃ fuel, lsemFuelMemL (singletonProgM fn body) fuel s = some t :=
  run_of_blockPath (memLMachine_sound (singletonProgM fn body)) h hfn

/-! ## 9. Block and edge counts on small bodies -/

/-- An instruction with source position `0`. -/
def li (i : LinstrR) : Linstr := ⟨0, i⟩

/-- A straight-line body of three instructions. -/
def straightBody (_ : Unit) : Lcmd :=
  [li (.Lopn [.reg "a"] "ADD_64" [.reg "a", .imm 1]),
   li (.Lopn [.reg "b"] "XOR_64" [.reg "b", .reg "a"]),
   li (.Lopn [.reg "a"] "MOV_64" [.reg "b"])]

/-- A counted loop: seed, `Llabel top`, body, counter test, back-edge, tail. -/
def loopBody (_ : Unit) : Lcmd :=
  [li (.Lopn [.reg "c"] "MOV_64" [.imm 4]),
   li (.Llabel .internal 1),
   li (.Lopn [.reg "a"] "ADD_64" [.reg "a", .imm 1]),
   li (.Lopn [.reg "c"] "SUB_64" [.reg "c", .imm 1]),
   li (.Lopn [.reg "c"] "CMP_64" [.reg "c", .imm 0]),
   li (.Lcond (.reg "NZ") 1),
   li (.Lopn [.reg "b"] "MOV_64" [.reg "a"]),
   li .Lret]

/-- A conditional: `Lcond ; else ; Lgoto end ; then: ; then ; end: ; tail`. -/
def ifBody (_ : Unit) : Lcmd :=
  [li (.Lcond (.reg "g") 2),
   li (.Lopn [.reg "a"] "MOV_64" [.imm 0]),
   li (.Lgoto ("f", 3)),
   li (.Llabel .internal 2),
   li (.Lopn [.reg "a"] "MOV_64" [.imm 1]),
   li (.Llabel .internal 3),
   li (.Lopn [.reg "b"] "MOV_64" [.reg "a"])]

/-- The block count and edge count of the graph of `c`. -/
def shape (c : Lcmd) : Option (Nat × Nat) :=
  (cfgOfLcmd c).map fun G => (G.blocks.size, G.numEdges)

set_option kat.ms 500 in
#kat shape [] == some (0, 0)
#kat shape (straightBody ()) == some (1, 0)
#kat shape (loopBody ()) == some (3, 3)
#kat shape (ifBody ()) == some (4, 4)
#kat (cfgOfLcmd (ifBody ())).bind (fun G => (G.labelOf ((ifBody ()).map Linstr.li_i) 3)) ==
  some 3
#kat (cfgOfLcmd (loopBody ())).map (fun G => G.predsOf 1) == some [0, 1]
-- A jump to an absent label.
#kat (cfgOfLcmd [li (.Lgoto ("f", 9)), li (.Llabel .internal 1)]).isNone
-- A duplicated label.
#kat (cfgOfLcmd [li (.Llabel .internal 1), li (.Llabel .internal 1)]).isNone
-- A call.
#kat (cfgOfLcmd [li (.Lcall none ("g", 0))]).isNone

end CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG
