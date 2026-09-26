/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad
public import CatCrypt.Crypto.SecureCompilation.VIR.LprogScheduler
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdReloadElim
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate
public import CatCrypt.Crypto.Optimizer.LoadCSE
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled
public import CatCrypt.Crypto.SecureCompilation.X86Backend.StackZeroize
public import CatCrypt.Crypto.Optimizer.ComRangeFold

/-!
# The `Lprog` optimization pipeline an emitter applies

`renderLprogAtt` is a pure printer. Every `Lprog → Lprog` pass is opt-in, so an
emitter that composes none of them renders the exporter's output verbatim. This
module names the composition an emitter applies, so the choice is made once
rather than per kernel.

## The passes in the chain

| pass | effect | guarantee |
|---|---|---|
| `LprogStoreToLoad.elimReloadsLprog` | drops a reload of a slot whose value is still held in the destination register | `elimReloads_sublist`, `elimReloads_length_le`: the output is a sublist of the input, so the pass only deletes |
| `LcmdReloadElim.reloadElimLprog` | drops a spill/reload pair around a clobbering instruction | `gatherRenderBody_sound` |
| `LprogScheduler.scheduleLprog` | reorders adjacent independent instructions | `scheduleBody_instr_multiset` (a permutation), `bubble_only_indep_swaps` (only independent pairs swap) |
| `LcmdCopyPropagate.copyPropagateLprog` | forwards a register copy to its uses and drops the copy | `copyPropagateBody_stateStore` (store-image equality on every body and every state) |
| `Optimizer.LoadCSE.loadCSELprog` | replaces a reload of a cached slot by a move from the register already holding it | `loadCSE_lsemStraight` (`lsemStraight`-equality on every body and every state), `loadCSE_mnems` (the output's mnemonic sequence equals the input's) |

`loadCSELprog` recognises only the `MOV:64` and `MOVQ` reload forms and declines
every other width, so it cannot re-emit a 64-bit move at a narrower width;
`loadCSE_widths` states that for any width assignment, including the printer's
`mnemWidth`.

## Main results

* `optimizeLprog` — the composition an emitter applies before `renderLprogAtt`.
* `ownedComStage`, `renderOwnedCom` — the opt-in `Com → Com` stage before the exporter
  (the range fold of `Optimizer.ComRangeFold`, off by default) and the back end from a
  `Com`; `ownedComStage_denote` — the stage's soundness.
* `optimizeLprogVerified` — the five passes with a semantic soundness theorem,
  and `optimizeVerifiedBody_stateStore` — the composed store-image preservation
  across those five passes.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem (lsemStraight Lstate)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust
  (stateStore ArchAgreeOpt archAgreeOpt_iff_stateStore)
open CatCrypt.Crypto.Optimizer.LoadCSE
  (loadCSE loadCSELprog loadCSELfundef loadCSE_lsemStraight)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogScheduler
  (scheduleBody scheduleLprog scheduleLfundef scheduleBody_lsemStraight)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdReloadElim
  (reloadElimBody reloadElimLprog reloadElimFundef reloadElimBody_lsem)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad
  (elimReloads elimReloadsLprog elimReloadsLfundef elimReloads_lsemStraight)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate
  (copyPropagateBody copyPropagateFundef copyPropagateLprog copyPropagateBody_stateStore
   copyPropagateBody_sublist_shape instrShape)

/-- The `Lprog → Lprog` chain an emitter applies before rendering: reload
    elimination, spill-pair elimination, scheduling, copy propagation, load
    common-subexpression elimination. -/
def optimizeLprog (p : Lprog) : Lprog :=
  CatCrypt.Crypto.Optimizer.LoadCSE.loadCSELprog
    (CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate.copyPropagateLprog
      (CatCrypt.Crypto.SecureCompilation.VIR.LprogScheduler.scheduleLprog
        (CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdReloadElim.reloadElimLprog
          (CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad.elimReloadsLprog p))))

/-! ## The verified sub-pipeline

The five passes with a semantic soundness theorem, in the order `optimizeLprog`
applies them: `elimReloadsLprog → reloadElimLprog → scheduleLprog →
copyPropagateLprog → loadCSELprog`.

The composed guarantee is an equality of the store image
(`Option.map stateStore ∘ lsemStraight`), not of the raw `lsemStraight` state.
Three of the five passes delete instructions — `elimReloads` drops a redundant
reload, `reloadElim` drops a spill/reload pair, `copyPropagateBody` forwards a
register copy and drops it — so the optimized body reaches the same register map
and memory but at a smaller program counter. The per-pass store lemmas match
this: `elimReloads_lsemStraight`, `reloadElimBody_lsem` and
`copyPropagateBody_stateStore` (store-image equalities, the latter two from an
`ArchAgreeOpt`) are store-level, while `scheduleBody_lsemStraight` and
`loadCSE_lsemStraight` are full `lsemStraight` equalities that imply the
store-level one. -/

/-- The sub-pipeline of the five passes with a semantic soundness theorem, in the
    order `optimizeLprog` applies them. -/
def optimizeLprogVerified (p : Lprog) : Lprog :=
  loadCSELprog (copyPropagateLprog (scheduleLprog (reloadElimLprog (elimReloadsLprog p))))

/-- The verified sub-pipeline on one function. -/
def optimizeVerifiedFundef (f : Lfundef) : Lfundef :=
  loadCSELfundef (copyPropagateFundef (scheduleLfundef (reloadElimFundef (elimReloadsLfundef f))))

/-- Every function body of the verified sub-pipeline's output is the four passes
    composed on that function's body. -/
theorem optimizeLprogVerified_funcs (p : Lprog) :
    (optimizeLprogVerified p).lp_funcs
      = p.lp_funcs.map (fun nf => (nf.1, optimizeVerifiedFundef nf.2)) := by
  dsimp only [optimizeLprogVerified, loadCSELprog, copyPropagateLprog, scheduleLprog,
    reloadElimLprog, elimReloadsLprog]
  simp only [List.map_map]
  apply List.map_congr_left
  rintro ⟨n, f⟩ _
  rfl

/-- The verified sub-pipeline preserves the function list and its symbol names. -/
theorem optimizeLprogVerified_names (p : Lprog) :
    (optimizeLprogVerified p).lp_funcs.map Prod.fst = p.lp_funcs.map Prod.fst := by
  simp [optimizeLprogVerified_funcs, List.map_map, Function.comp_def]

/-- **Composed soundness, per function body.** On every start state, the five
    verified passes leave the store (register map and memory) unchanged. The
    equality is of the store image `Option.map stateStore ∘ lsemStraight`: the
    three deletion passes lower the program counter, so the raw state differs
    while its store does not. Proven by chaining the two full `lsemStraight`
    equalities (`loadCSE`, `scheduleBody`) with the three store-level lemmas
    (`copyPropagateBody`, `reloadElimBody`, `elimReloads`) through
    `archAgreeOpt_iff_stateStore`. -/
theorem optimizeVerifiedBody_stateStore {w : Nat} (body : List Linstr) (s : Lstate w) :
    Option.map stateStore
        (lsemStraight
          ((loadCSE (copyPropagateBody
            (scheduleBody (reloadElimBody (elimReloads body))))).map Linstr.li_i) s)
      = Option.map stateStore (lsemStraight (body.map Linstr.li_i) s) := by
  rw [loadCSE_lsemStraight, copyPropagateBody_stateStore, scheduleBody_lsemStraight,
    (archAgreeOpt_iff_stateStore _ _).mp (reloadElimBody_lsem (elimReloads body) s)]
  exact elimReloads_lsemStraight body s

/-- **Composed soundness on one function.** The optimized function's body reaches
    the same store as the original from every start state. -/
theorem optimizeVerifiedFundef_stateStore {w : Nat} (f : Lfundef) (s : Lstate w) :
    Option.map stateStore
        (lsemStraight ((optimizeVerifiedFundef f).lfd_body.map Linstr.li_i) s)
      = Option.map stateStore (lsemStraight (f.lfd_body.map Linstr.li_i) s) :=
  optimizeVerifiedBody_stateStore f.lfd_body s

/-- A function body is straight-line — no loop or branch control flow — when it
    holds no label or jump instruction. `Lcall` is permitted: a call is a barrier
    the straight-line passes treat as opaque and do not reorder across (the
    `p2_sponge` leaf-call kernel is straight-line by this test). The verified
    passes' soundness is stated for `lsemStraight`, so only bodies passing this
    test may be optimized. -/
def bodyIsStraightLine (body : List Linstr) : Bool :=
  body.all fun i => match i.li_i with
    | .Llabel _ _ => false
    | .Lgoto _    => false
    | .Ligoto _   => false
    | .Lcond _ _  => false
    | .Lret       => false
    | _           => true

/-! ## Per-basic-block optimization of a control-flow body

A body is a sequence of maximal straight-line runs separated by control-flow
instructions (labels and jumps). `splitStraightRuns` partitions it so each
control-flow instruction is its own singleton segment and each maximal run of
straight-line instructions is one segment; `optimizeBasicBlocks` applies the
verified sub-pipeline to every straight-line run and leaves the control-flow
segments verbatim. On a straight-line body this equals `optimizeVerifiedFundef`'s
body transform, so it extends the guarded pipeline rather than replacing it. -/

/-- An instruction is control flow — a label or a jump — rather than a
    straight-line word operation. `bodyIsStraightLine` is the negation of this
    predicate lifted over the body. -/
def isCtlInstr (i : Linstr) : Bool :=
  match i.li_i with
  | .Llabel _ _ => true
  | .Lgoto _    => true
  | .Ligoto _   => true
  | .Lcond _ _  => true
  | .Lret       => true
  | _           => false

/-- An instruction is inside the modeled straight-line fragment: a single
    register-destination `Lopn` whose stripped mnemonic and source arity match
    a modeled opcode. These are `JasminLsem.applyOpn`'s word opcodes
    (`ADD`/`SUB`/`MUL`/`AND`/`OR`/`XOR`/`SHL`/`SHR`/`ANDN`/`MULXHI` on two
    sources, `ADCX`/`ADCXHI` on three, `MOV`/`MOVQ` on one) together with the two
    runtime-indexed memory opcodes `LOADIDX` (a register load, one `.arrIdx`
    source) and `STOREIDX` (a memory write, an `.arrIdx` source and a value
    source). On any other instruction `lsemStep`/`lsemStraight` return `none`, so
    a store-image guarantee over it would be vacuous. -/
def instrModeled (i : Linstr) : Bool :=
  match i.li_i with
  | .Lopn [.reg _] opn srcs =>
      match stripWidthTag opn, srcs.length with
      | "ADD", 2 => true
      | "SUB", 2 => true
      | "MUL", 2 => true
      | "AND", 2 => true
      | "OR", 2 => true
      | "XOR", 2 => true
      | "SHL", 2 => true
      | "SHR", 2 => true
      | "ANDN", 2 => true
      | "MULXHI", 2 => true
      | "ADCX", 3 => true
      | "ADCXHI", 3 => true
      | "MOV", 1 => true
      | "MOVQ", 1 => true
      -- Narrow ABI buffer moves (`abiMovBuf`): the zero-extending `movzbl` /
      -- `movzwl` load of a byte / word-packed C-buffer element, and the width-exact
      -- `movb` / `movw` store. `stripWidthTag` peels only `:64`, so the `:8` / `:16`
      -- tag survives; `JasminLsem.applyOpn` models both directions as the low-bits
      -- keep of the single source.
      | "MOV:8", 1 => true
      | "MOV:16", 1 => true
      | "LOADIDX", 1 => true
      | "STOREIDX", 2 => true
      -- Count-tagged immediate shift / rotate (`SHL:0`, `SHR:32`, `SAR:k`,
      -- `ROL:k`, `ROR:k`): a single-source op whose mnemonic carries the shift
      -- count. `stripWidthTag` keeps the count tag, so these do not match a bare
      -- opcode literal; `parseImmShiftMnem` reads the direction and count off the
      -- raw mnemonic. `JasminLsem.applyOpn` models them on their one source.
      | _, 1 =>
          (CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.parseImmShiftMnem
            opn).isSome
      | _, _ => false
  | _ => false

/-- Every instruction of the body is inside the modeled word fragment
    (`instrModeled`); only such a body has a non-vacuous `lsemStraight`. -/
def bodyAllModeled (body : List Linstr) : Bool := body.all instrModeled

/-- The verified sub-pipeline as a body transform on one straight-line run:
    reload elimination, spill-pair elimination, scheduling, copy propagation,
    load-CSE — applied only when every instruction is inside the modeled word
    fragment (`bodyAllModeled`). A body with an unmodeled op (for instance
    `vpshufb`) is returned verbatim, so the optimizer never reorders or deletes an
    instruction whose semantics the store-image guarantee cannot see. -/
def optRunBody (body : List Linstr) : List Linstr :=
  if bodyAllModeled body then
    loadCSE (copyPropagateBody (scheduleBody (reloadElimBody (elimReloads body))))
  else body

/-- Every pass fixes the empty body, so the composed body transform does too. -/
theorem optRunBody_nil : optRunBody ([] : List Linstr) = [] := by
  simp [optRunBody, bodyAllModeled, loadCSE, copyPropagateBody, scheduleBody,
    CatCrypt.Crypto.SecureCompilation.VIR.LprogScheduler.bubbleNEarly, reloadElimBody,
    elimReloads, CatCrypt.Crypto.Optimizer.LoadCSE.loadCSEAuxImpl,
    CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate.deadElimBody,
    CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate.propagateAux,
    CatCrypt.Crypto.SecureCompilation.VIR.LprogScheduler.bubbleN]

/-- `optRunBody` on one straight-line run preserves the store image
    (`Option.map stateStore ∘ lsemStraight`) from every start state. On a body
    outside the modeled fragment the pass is the identity, so the store image is
    literally unchanged; on a modeled body it is the four verified passes. -/
theorem optRunBody_stateStore {w : Nat} (body : List Linstr) (s : Lstate w) :
    Option.map stateStore (lsemStraight ((optRunBody body).map Linstr.li_i) s)
      = Option.map stateStore (lsemStraight (body.map Linstr.li_i) s) := by
  unfold optRunBody
  by_cases hm : bodyAllModeled body = true
  · rw [if_pos hm]; exact optimizeVerifiedBody_stateStore body s
  · rw [if_neg hm]

/-- `bodyIsStraightLine` on a cons: the head is not a control-flow instruction and
    the tail is straight-line. -/
theorem bodyIsStraightLine_cons (i : Linstr) (rest : List Linstr) :
    bodyIsStraightLine (i :: rest) = (!isCtlInstr i && bodyIsStraightLine rest) := by
  simp only [bodyIsStraightLine, List.all_cons]
  congr 1
  unfold isCtlInstr
  cases i.li_i <;> rfl

/-- Partition a body into segments, threading a straight-line run in `cur`. A
    control-flow instruction flushes `cur` and becomes its own singleton segment;
    a straight-line instruction extends `cur`. -/
def splitStraightRunsAux : List Linstr → List Linstr → List (List Linstr)
  | cur, [] => if cur.isEmpty then [] else [cur]
  | cur, i :: rest =>
      if isCtlInstr i then
        (if cur.isEmpty then [] else [cur]) ++ ([i] :: splitStraightRunsAux [] rest)
      else
        splitStraightRunsAux (cur ++ [i]) rest

/-- Partition a body into maximal straight-line runs with each control-flow
    instruction as a singleton boundary segment. -/
def splitStraightRuns (body : List Linstr) : List (List Linstr) :=
  splitStraightRunsAux [] body

/-- The partition reconstructs the body: concatenating the accumulator with the
    flattened segments recovers `cur ++ body`. -/
theorem splitStraightRunsAux_flatten (cur body : List Linstr) :
    (splitStraightRunsAux cur body).flatten = cur ++ body := by
  induction body generalizing cur with
  | nil => cases cur <;> simp [splitStraightRunsAux]
  | cons i rest ih =>
      unfold splitStraightRunsAux
      by_cases hci : isCtlInstr i = true
      · simp only [hci, if_true]
        cases cur with
        | nil => simp [ih]
        | cons c cs => simp [ih]
      · simp only [Bool.not_eq_true] at hci
        simp only [hci, Bool.false_eq_true, if_false, ih (cur ++ [i]),
          List.append_assoc, List.singleton_append]

/-- The partition reconstructs the body verbatim: control-flow instructions and
    the straight-line runs together flatten back to the original. -/
theorem splitStraightRuns_flatten (body : List Linstr) :
    (splitStraightRuns body).flatten = body := by
  simpa using! splitStraightRunsAux_flatten [] body

/-- Map the verified sub-pipeline over each straight-line run, leaving the
    control-flow segments unchanged, and concatenate. -/
def optimizeBasicBlocks (body : List Linstr) : List Linstr :=
  ((splitStraightRuns body).map
    (fun seg => if bodyIsStraightLine seg then optRunBody seg else seg)).flatten

/-- On a straight-line body the partition is a single run (empty for an empty
    body). -/
theorem splitStraightRunsAux_straight (body cur : List Linstr)
    (h : bodyIsStraightLine body = true) :
    splitStraightRunsAux cur body = if (cur ++ body).isEmpty then [] else [cur ++ body] := by
  induction body generalizing cur with
  | nil => simp [splitStraightRunsAux]
  | cons i rest ih =>
      rw [bodyIsStraightLine_cons, Bool.and_eq_true] at h
      obtain ⟨hi, hrest⟩ := h
      have hci : isCtlInstr i = false := by
        cases hh : isCtlInstr i with
        | false => rfl
        | true => rw [hh] at hi; exact absurd hi (by decide)
      unfold splitStraightRunsAux
      simp only [hci, Bool.false_eq_true, if_false, ih (cur ++ [i]) hrest,
        List.append_assoc, List.singleton_append]

/-- On a straight-line body `optimizeBasicBlocks` is exactly the verified
    sub-pipeline's body transform. -/
theorem optimizeBasicBlocks_straight (body : List Linstr)
    (h : bodyIsStraightLine body = true) :
    optimizeBasicBlocks body = optRunBody body := by
  unfold optimizeBasicBlocks splitStraightRuns
  rw [splitStraightRunsAux_straight body [] h, List.nil_append]
  cases body with
  | nil => rw [optRunBody_nil]; simp
  | cons i rest =>
      simp only [Bool.false_eq_true, if_false, List.isEmpty_cons, List.map_cons,
        List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, if_pos h]

/-- On a straight-line body `optimizeBasicBlocks` preserves the store image from
    every start state — the per-run soundness lifted through the single-run
    partition. -/
theorem optimizeBasicBlocks_straight_stateStore {w : Nat} (body : List Linstr)
    (h : bodyIsStraightLine body = true) (s : Lstate w) :
    Option.map stateStore (lsemStraight ((optimizeBasicBlocks body).map Linstr.li_i) s)
      = Option.map stateStore (lsemStraight (body.map Linstr.li_i) s) := by
  rw [optimizeBasicBlocks_straight body h]
  exact optRunBody_stateStore body s

/-- On a straight-line, all-modeled function body `optimizeBasicBlocks` equals the
    guarded pipeline's body. Outside the modeled fragment `optRunBody` is the
    identity, so the equation needs the `bodyAllModeled` hypothesis. -/
theorem optimizeBasicBlocks_eq_guarded (f : Lfundef)
    (h : bodyIsStraightLine f.lfd_body = true) (hm : bodyAllModeled f.lfd_body = true) :
    optimizeBasicBlocks f.lfd_body = (optimizeVerifiedFundef f).lfd_body := by
  rw [optimizeBasicBlocks_straight f.lfd_body h, optRunBody, if_pos hm]
  rfl

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust (lsemStep_stateStore)
open CatCrypt.Crypto.Optimizer.LoadCSE (loadCSE_eq loadCSEAux loadCSEAux_cons stepLoad asWideReload LoadEnv)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogScheduler (scheduleBody_instr_multiset)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdReloadElim (reloadElimBody_sublist)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad (elimReloads_sublist)

/-! ## Full control-flow-graph soundness for per-basic-block optimization

`mapBodies optimizeBasicBlocks` optimizes the straight-line runs of every
function body over the labeled, program-counter-indexed semantics
`JasminLsemLabeled.lsem`. `Sim` is the forward simulation relating a source pc
to the optimized pc in the same basic block with equal store; `sim_main` is the
strong-induction simulation over fuel; `mapBodies_entry_store_preserved` is the
`lsem`-level store-image preservation from a function entry. -/

def optSeg (seg : List Linstr) : List Linstr := if bodyIsStraightLine seg then optRunBody seg else seg
def NotBranch (i : LinstrR) : Bool := match i with | .Lgoto _ => false | .Lcond _ _ => false | _ => true
def isLbl (i : LinstrR) : Bool := match i with | .Llabel _ _ => true | _ => false
def mapBodies (f : List Linstr → List Linstr) (P : Lprog) : Lprog :=
  { P with lp_funcs := P.lp_funcs.map (fun nf => (nf.1, { nf.2 with lfd_body := f nf.2.lfd_body })) }
def bdry (segs : List (List Linstr)) (k : Nat) : Nat := ((segs.take k).flatten).length
def obdry (segs : List (List Linstr)) (k : Nat) : Nat := (((segs.take k).map optSeg).flatten).length
theorem optimizeBasicBlocks_eq_optSeg (body : List Linstr) :
    optimizeBasicBlocks body = ((splitStraightRuns body).map optSeg).flatten := rfl

theorem lsemStep_lpc_succ' {w} (i : LinstrR) (s b : Lstate w)
    (h : lsemStep i s = some b) : b.lpc = s.lpc + 1 := by
  cases i with
  | Lopn dsts opn srcs =>
      cases dsts with
      | nil => simp [lsemStep] at h
      | cons d ds =>
        cases ds with
        | cons _ _ => simp [lsemStep] at h
        | nil =>
          cases d with
          | reg dst =>
            cases srcs with
            | nil =>
                simp only [lsemStep] at h
                cases happ : applyOpn (stripWidthTag opn)
                    (List.map (evalOperand s) ([] : List LOperand)) with
                | none => rw [happ] at h; simp at h
                | some v =>
                    rw [happ] at h; simp only [Option.some.injEq] at h; rw [← h]; rfl
            | cons hd rest =>
                cases hd with
                | reg r =>
                    rw [lsemStep_reg_srcs dst opn (LOperand.reg r :: rest) s
                      (by intro b i sc rst; simp)] at h
                    cases happ : applyOpn (stripWidthTag opn)
                        (List.map (evalOperand s) (LOperand.reg r :: rest)) with
                    | none => rw [happ] at h; simp at h
                    | some v =>
                        rw [happ] at h; simp only [Option.some.injEq] at h; rw [← h]; rfl
                | imm im =>
                    rw [lsemStep_reg_srcs dst opn (LOperand.imm im :: rest) s
                      (by intro b i sc rst; simp)] at h
                    cases happ : applyOpn (stripWidthTag opn)
                        (List.map (evalOperand s) (LOperand.imm im :: rest)) with
                    | none => rw [happ] at h; simp at h
                    | some v =>
                        rw [happ] at h; simp only [Option.some.injEq] at h; rw [← h]; rfl
                | arr a o =>
                    rw [lsemStep_reg_srcs dst opn (LOperand.arr a o :: rest) s
                      (by intro b i sc rst; simp)] at h
                    cases happ : applyOpn (stripWidthTag opn)
                        (List.map (evalOperand s) (LOperand.arr a o :: rest)) with
                    | none => rw [happ] at h; simp at h
                    | some v =>
                        rw [happ] at h; simp only [Option.some.injEq] at h; rw [← h]; rfl
                | arrIdx base idx scale =>
                    simp only [lsemStep] at h
                    by_cases hL : opn = "LOADIDX"
                    · rw [if_pos hL] at h
                      simp only [Option.some.injEq] at h; rw [← h]; rfl
                    · rw [if_neg hL] at h
                      by_cases hS : opn = "STOREIDX"
                      · rw [if_pos hS] at h
                        cases rest with
                        | nil => simp at h
                        | cons val vrest =>
                            cases vrest with
                            | nil =>
                                simp only [Option.some.injEq] at h; rw [← h]; rfl
                            | cons _ _ => simp at h
                      · rw [if_neg hS] at h
                        cases happ : applyOpn (stripWidthTag opn)
                            (List.map (evalOperand s)
                              (LOperand.arrIdx base idx scale :: rest)) with
                        | none => rw [happ] at h; simp at h
                        | some v =>
                            rw [happ] at h; simp only [Option.some.injEq] at h
                            rw [← h]; rfl
          | imm _ => simp [lsemStep] at h
          | arr _ _ => simp [lsemStep] at h
          | arrIdx _ _ _ => simp [lsemStep] at h
  | Lalign => simp only [lsemStep, Option.some.injEq] at h; rw [← h]; rfl
  | Llabel k l => simp only [lsemStep, Option.some.injEq] at h; rw [← h]; rfl
  | Lgoto _ => simp [lsemStep] at h
  | Lcond _ _ => simp [lsemStep] at h
  | Ligoto _ => simp [lsemStep] at h
  | Lcall _ _ => simp [lsemStep] at h
  | Lret => simp [lsemStep] at h
  | LstoreLabel _ _ => simp [lsemStep] at h
  | Lsyscall _ => simp [lsemStep] at h

theorem evalInstrP_notBranch (P : Lprog) {w} (i : LinstrR) (s : LstateP w)
    (h : NotBranch i = true) :
    evalInstrP P i s = (lsemStep i s.base).map (fun b => { s with base := b }) := by
  cases i <;> first | rfl | (simp [NotBranch] at h)

theorem findInstr_body (P : Lprog) (fn : String) (fd : Lfundef)
    (hfd : getFundef P fn = some fd) {w} (s : LstateP w) (hfn : s.lfn = fn) :
    findInstr P s = (fd.lfd_body.map Linstr.li_i)[s.base.lpc]? := by
  simp only [findInstr, hfn, hfd, List.getElem?_map]

theorem evalOperand_congr {w} {s t : Lstate w} (h : stateStore s = stateStore t)
    (o : LOperand) : evalOperand s o = evalOperand t o := by
  simp only [stateStore, Prod.mk.injEq] at h
  obtain ⟨hv, hm⟩ := h
  cases o <;> simp [evalOperand, hv, hm]

theorem lsemStraight_stateStore {w} (is : List LinstrR) {s t : Lstate w}
    (h : stateStore s = stateStore t) :
    Option.map stateStore (lsemStraight is s) = Option.map stateStore (lsemStraight is t) := by
  induction is generalizing s t with
  | nil => simp [h]
  | cons i is ih =>
    simp only [lsemStraight_cons]
    have hstep := lsemStep_stateStore i h
    cases hs : lsemStep i s with
    | none =>
      rw [hs] at hstep
      cases ht : lsemStep i t with
      | none => simp
      | some t1 => rw [ht] at hstep; simp at hstep
    | some s1 =>
      rw [hs] at hstep
      cases ht : lsemStep i t with
      | none => rw [ht] at hstep; simp at hstep
      | some t1 => rw [ht] at hstep; exact ih (Option.some.inj hstep)

theorem fetch_head (bodyR preR is postR : List LinstrR) (i : LinstrR)
    (hbody : bodyR = preR ++ (i :: is) ++ postR) : bodyR[preR.length]? = some i := by
  have hb : bodyR = preR ++ ((i :: is) ++ postR) := by rw [hbody, List.append_assoc]
  rw [hb, List.getElem?_append_right (Nat.le_refl _)]
  simp

theorem runForward (P : Lprog) (fn : String) {w} (bodyR : List LinstrR)
    (Hfetch : ∀ (u : LstateP w), u.lfn = fn → findInstr P u = bodyR[u.base.lpc]?) :
    ∀ (runR : List LinstrR), (∀ i ∈ runR, NotBranch i = true) →
    ∀ (preR postR : List LinstrR), bodyR = preR ++ runR ++ postR →
    ∀ (s : LstateP w), s.lfn = fn → s.base.lpc = preR.length →
    ∀ (b : Lstate w), lsemStraight runR s.base = some b →
    ∀ rest, lsemFuel P (runR.length + rest) s
      = lsemFuel P rest ⟨{ b with lpc := preR.length + runR.length }, fn⟩ := by
  intro runR
  induction runR with
  | nil =>
    intro _ preR postR _ s hfn hpc b hstraight rest
    simp only [lsemStraight_nil, Option.some.injEq] at hstraight
    subst hstraight
    have hb : ({ s.base with lpc := preR.length } : Lstate w) = s.base := by rw [← hpc]
    have hs : (⟨{ s.base with lpc := preR.length }, fn⟩ : LstateP w) = s := by rw [hb, ← hfn]
    simp only [List.length_nil, Nat.zero_add, Nat.add_zero, hs]
  | cons i is ih =>
    intro hnb preR postR hbody s hfn hpc b hstraight rest
    have hnbi : NotBranch i = true := hnb i (List.mem_cons_self ..)
    have hnbs : ∀ j ∈ is, NotBranch j = true := fun j hj => hnb j (List.mem_cons_of_mem _ hj)
    have hfetch : findInstr P s = some i := by
      rw [Hfetch s hfn, hpc]; exact fetch_head bodyR preR is postR i hbody
    simp only [lsemStraight_cons] at hstraight
    cases hs : lsemStep i s.base with
    | none => simp [hs] at hstraight
    | some b1 =>
      simp only [hs] at hstraight
      have hb1pc : b1.lpc = preR.length + 1 := by rw [lsemStep_lpc_succ' i s.base b1 hs, hpc]
      have hbody' : bodyR = (preR ++ [i]) ++ is ++ postR := by rw [hbody]; simp
      have hstep : evalInstrP P i s = some ⟨b1, fn⟩ := by
        rw [evalInstrP_notBranch P i s hnbi, hs]; simp [hfn]
      have key := ih hnbs (preR ++ [i]) postR hbody' ⟨b1, fn⟩ rfl (by simp [hb1pc]) b hstraight rest
      have harith : (i :: is).length + rest = (is.length + rest) + 1 := by
        simp only [List.length_cons]; omega
      have hlpc : preR.length + (i :: is).length = (preR ++ [i]).length + is.length := by
        simp only [List.length_cons, List.length_append, List.length_nil]; omega
      rw [harith]
      simp only [lsemFuel, hfetch, hstep]
      rw [hlpc]
      exact key

theorem fuelRun (P : Lprog) (fn : String) {w} (bodyR : List LinstrR)
    (Hfetch : ∀ (u : LstateP w), u.lfn = fn → findInstr P u = bodyR[u.base.lpc]?) :
    ∀ (runR : List LinstrR), (∀ i ∈ runR, NotBranch i = true) →
    ∀ (preR postR : List LinstrR), bodyR = preR ++ runR ++ postR →
    ∀ (s : LstateP w), s.lfn = fn → s.base.lpc = preR.length →
    ∀ (fuel : Nat) (t : LstateP w), lsemFuel P fuel s = some t →
    ∃ b, lsemStraight runR s.base = some b ∧ runR.length ≤ fuel ∧
         lsemFuel P (fuel - runR.length) ⟨{ b with lpc := preR.length + runR.length }, fn⟩ = some t := by
  intro runR
  induction runR with
  | nil =>
    intro _ preR postR _ s hfn hpc fuel t hfuel
    refine ⟨s.base, rfl, Nat.zero_le _, ?_⟩
    have hb : ({ s.base with lpc := preR.length } : Lstate w) = s.base := by rw [← hpc]
    have hs : (⟨{ s.base with lpc := preR.length }, fn⟩ : LstateP w) = s := by rw [hb, ← hfn]
    simpa [hs] using hfuel
  | cons i is ih =>
    intro hnb preR postR hbody s hfn hpc fuel t hfuel
    have hnbi : NotBranch i = true := hnb i (List.mem_cons_self ..)
    have hnbs : ∀ j ∈ is, NotBranch j = true := fun j hj => hnb j (List.mem_cons_of_mem _ hj)
    have hfetch : findInstr P s = some i := by
      rw [Hfetch s hfn, hpc]; exact fetch_head bodyR preR is postR i hbody
    cases fuel with
    | zero => simp [lsemFuel, hfetch] at hfuel
    | succ f =>
      simp only [lsemFuel, hfetch, evalInstrP_notBranch P i s hnbi] at hfuel
      cases hs : lsemStep i s.base with
      | none => simp [hs] at hfuel
      | some b1 =>
        simp only [hs, Option.map_some] at hfuel
        rw [hfn] at hfuel
        have hb1pc : b1.lpc = preR.length + 1 := by rw [lsemStep_lpc_succ' i s.base b1 hs, hpc]
        have hbody' : bodyR = (preR ++ [i]) ++ is ++ postR := by rw [hbody]; simp
        obtain ⟨b, hstr, hle, htail⟩ :=
          ih hnbs (preR ++ [i]) postR hbody' ⟨b1, fn⟩ rfl (by simp [hb1pc]) f t hfuel
        refine ⟨b, ?_, ?_, ?_⟩
        · simp only [lsemStraight_cons, hs]; exact hstr
        · rw [List.length_cons]; omega
        · have hlpc : preR.length + (i :: is).length = (preR ++ [i]).length + is.length := by
            simp only [List.length_cons, List.length_append, List.length_nil]; omega
          have hf : (f + 1) - (i :: is).length = f - is.length := by
            simp only [List.length_cons]; omega
          rw [hf, hlpc]; exact htail

theorem getFundef_mapBodies (f : List Linstr → List Linstr) (P : Lprog) (fn : String) :
    getFundef (mapBodies f P) fn = (getFundef P fn).map (fun fd => { fd with lfd_body := f fd.lfd_body }) := by
  simp only [getFundef, mapBodies, List.find?_map, Option.map_map]
  rfl

theorem flatten_decomp {α} (segs : List (List α)) (k : Nat) (hk : k < segs.length) :
    segs.flatten = (segs.take k).flatten ++ segs[k] ++ (segs.drop (k + 1)).flatten := by
  conv_lhs => rw [← List.take_append_drop k segs, List.drop_eq_getElem_cons hk]
  simp only [List.flatten_append, List.flatten_cons, List.append_assoc]

theorem bodyIsStraightLine_append (l1 l2 : List Linstr) :
    bodyIsStraightLine (l1 ++ l2) = (bodyIsStraightLine l1 && bodyIsStraightLine l2) := by
  simp only [bodyIsStraightLine, List.all_append]

theorem straight_singleton_of_not_ctl (i : Linstr) (h : isCtlInstr i = false) :
    bodyIsStraightLine [i] = true := by
  simp only [bodyIsStraightLine, List.all_cons, List.all_nil, Bool.and_true]
  unfold isCtlInstr at h
  revert h
  cases i.li_i <;> simp

theorem splitAux_good (body cur : List Linstr) (hcur : bodyIsStraightLine cur = true) :
    ∀ seg ∈ splitStraightRunsAux cur body,
      seg ≠ [] ∧ ((∃ c, seg = [c] ∧ isCtlInstr c = true) ∨ bodyIsStraightLine seg = true) := by
  induction body generalizing cur with
  | nil =>
    intro seg hseg
    simp only [splitStraightRunsAux] at hseg
    by_cases hce : cur.isEmpty = true
    · rw [if_pos hce] at hseg; simp at hseg
    · rw [if_neg hce] at hseg
      simp only [List.mem_singleton] at hseg
      subst hseg
      exact ⟨fun h => hce (by simp [h]), Or.inr hcur⟩
  | cons i rest ih =>
    intro seg hseg
    unfold splitStraightRunsAux at hseg
    by_cases hci : isCtlInstr i = true
    · rw [if_pos hci] at hseg
      by_cases hce : cur.isEmpty = true
      · rw [if_pos hce, List.nil_append] at hseg
        simp only [List.mem_cons] at hseg
        rcases hseg with h | h
        · subst h; exact ⟨by simp, Or.inl ⟨i, rfl, hci⟩⟩
        · exact ih [] (by simp [bodyIsStraightLine]) seg h
      · rw [if_neg hce] at hseg
        simp only [List.cons_append, List.nil_append, List.mem_cons] at hseg
        rcases hseg with h | h | h
        · subst h; exact ⟨fun he => hce (by simp [he]), Or.inr hcur⟩
        · subst h; exact ⟨by simp, Or.inl ⟨i, rfl, hci⟩⟩
        · exact ih [] (by simp [bodyIsStraightLine]) seg h
    · have hcif : isCtlInstr i = false := by
        cases hh : isCtlInstr i with
        | false => rfl
        | true => exact absurd hh hci
      rw [if_neg hci] at hseg
      have hcur' : bodyIsStraightLine (cur ++ [i]) = true := by
        simp [bodyIsStraightLine_append, hcur, straight_singleton_of_not_ctl i hcif]
      exact ih (cur ++ [i]) hcur' seg hseg

theorem splitStraightRuns_good (body : List Linstr) :
    ∀ seg ∈ splitStraightRuns body,
      seg ≠ [] ∧ ((∃ c, seg = [c] ∧ isCtlInstr c = true) ∨ bodyIsStraightLine seg = true) :=
  splitAux_good body [] (by simp [bodyIsStraightLine])

theorem bdry_succ (segs : List (List Linstr)) (k : Nat) (hk : k < segs.length) :
    bdry segs (k + 1) = bdry segs k + (segs[k]).length := by
  unfold bdry
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [Option.toList_some, List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.length_append]

theorem obdry_succ (segs : List (List Linstr)) (k : Nat) (hk : k < segs.length) :
    obdry segs (k + 1) = obdry segs k + (optSeg (segs[k])).length := by
  unfold obdry
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil,
    List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append]

theorem bdry_full (segs : List (List Linstr)) : bdry segs segs.length = segs.flatten.length := by
  unfold bdry; rw [List.take_length]

theorem obdry_full (segs : List (List Linstr)) :
    obdry segs segs.length = ((segs.map optSeg).flatten).length := by
  unfold obdry; rw [List.take_length]

/-- The forward simulation relating a source state and an optimized state: same
    current function, both at the start of the same basic-block index, equal store. -/
def Sim (P : Lprog) {w : Nat} (s s' : LstateP w) : Prop :=
  ∃ (fd : Lfundef) (k : Nat),
    getFundef P s.lfn = some fd ∧ s'.lfn = s.lfn ∧
    k ≤ (splitStraightRuns fd.lfd_body).length ∧
    s.base.lpc = bdry (splitStraightRuns fd.lfd_body) k ∧
    s'.base.lpc = obdry (splitStraightRuns fd.lfd_body) k ∧
    stateStore s.base = stateStore s'.base

theorem notBranch_of_lsemStep_some (i : LinstrR) {w} (s b : Lstate w)
    (h : lsemStep i s = some b) : NotBranch i = true := by
  cases i <;> first | rfl | (simp [lsemStep] at h)

theorem notBranch_of_straight (seg : List Linstr) (h : bodyIsStraightLine seg = true)
    (i : LinstrR) (hi : i ∈ seg.map Linstr.li_i) : NotBranch i = true := by
  rw [List.mem_map] at hi
  obtain ⟨x, hx, hxi⟩ := hi
  subst hxi
  rw [bodyIsStraightLine, List.all_eq_true] at h
  have hxv := h x hx
  revert hxv
  unfold NotBranch
  cases x.li_i <;> simp

theorem isLbl_of_isLabel (lbl : LLabel) (i : LinstrR) (h : isLabel lbl i = true) : isLbl i = true := by
  cases i <;> simp_all [isLabel, isLbl]

theorem stepLoad_li_i_cases (h : LoadEnv) (i : Linstr) :
    (stepLoad h i).1.li_i = i.li_i ∨ ∃ a b c, (stepLoad h i).1.li_i = .Lopn a b c := by
  unfold stepLoad
  split
  · split
    · split
      · exact Or.inl rfl
      · exact Or.inr ⟨_, _, _, rfl⟩
    · exact Or.inl rfl
  · exact Or.inl rfl

theorem loadCSEAux_noLabel (h : LoadEnv) (body : List Linstr)
    (hb : ∀ i ∈ body, isLbl i.li_i = false) :
    ∀ i ∈ loadCSEAux h body, isLbl i.li_i = false := by
  induction body generalizing h with
  | nil => intro i hi; simp at hi
  | cons j js ih =>
    intro i hi
    rw [loadCSEAux_cons] at hi
    rcases List.mem_cons.mp hi with rfl | hmem
    · rcases stepLoad_li_i_cases h j with heq | ⟨a, b, c, heq⟩
      · rw [heq]; exact hb j (List.mem_cons_self ..)
      · rw [heq]; rfl
    · exact ih (stepLoad h j).2 (fun x hx => hb x (List.mem_cons_of_mem _ hx)) i hmem

theorem loadCSE_noLabel (body : List Linstr) (hb : ∀ i ∈ body, isLbl i.li_i = false) :
    ∀ i ∈ loadCSE body, isLbl i.li_i = false := by
  rw [loadCSE_eq]; exact loadCSEAux_noLabel _ body hb

theorem straightLine_noLabel (seg : List Linstr) (h : bodyIsStraightLine seg = true) :
    ∀ i ∈ seg, isLbl i.li_i = false := by
  rw [bodyIsStraightLine, List.all_eq_true] at h
  intro i hi
  have := h i hi
  revert this; cases i.li_i <;> simp [isLbl]

/-- `isLbl` reads off `instrShape`: only a label's shape carries a whole
    `Llabel` instruction in its `.2.2` component. -/
theorem isLbl_eq_shape (i : Linstr) :
    isLbl i.li_i
      = (match (instrShape i).2.2 with | some (.Llabel _ _) => true | _ => false) := by
  obtain ⟨ii, li⟩ := i
  cases li <;> rfl

/-- Copy propagation preserves the absence of labels: its output shapes are a
    sublist of the input's (`copyPropagateBody_sublist_shape`), and `isLbl` is a
    function of the shape. -/
theorem copyPropagateBody_noLabel (body : List Linstr)
    (hb : ∀ i ∈ body, isLbl i.li_i = false) :
    ∀ i ∈ copyPropagateBody body, isLbl i.li_i = false := by
  intro j hj
  have hmem : instrShape j ∈ (copyPropagateBody body).map instrShape :=
    List.mem_map_of_mem hj
  have hsub := (copyPropagateBody_sublist_shape body).subset hmem
  rw [List.mem_map] at hsub
  obtain ⟨i, hi, hshape⟩ := hsub
  rw [isLbl_eq_shape j, ← hshape, ← isLbl_eq_shape i]
  exact hb i hi

theorem optRunBody_noLabel (seg : List Linstr) (hsl : bodyIsStraightLine seg = true) :
    ∀ i ∈ optRunBody seg, isLbl i.li_i = false := by
  have h0 : ∀ i ∈ seg, isLbl i.li_i = false := straightLine_noLabel seg hsl
  unfold optRunBody
  by_cases hm : bodyAllModeled seg = true
  · rw [if_pos hm]
    have h1 : ∀ i ∈ elimReloads seg, isLbl i.li_i = false :=
      fun i hi => h0 i ((elimReloads_sublist seg).mem hi)
    have h2 : ∀ i ∈ reloadElimBody (elimReloads seg), isLbl i.li_i = false :=
      fun i hi => h1 i ((reloadElimBody_sublist _).mem hi)
    have h3 : ∀ i ∈ scheduleBody (reloadElimBody (elimReloads seg)), isLbl i.li_i = false := by
      intro i hi
      have hmem : i.li_i ∈ (scheduleBody (reloadElimBody (elimReloads seg))).map Linstr.li_i :=
        List.mem_map_of_mem hi
      rw [(scheduleBody_instr_multiset _).mem_iff] at hmem
      rw [List.mem_map] at hmem
      obtain ⟨x, hx, hxeq⟩ := hmem
      rw [← hxeq]; exact h2 x hx
    exact loadCSE_noLabel _ (copyPropagateBody_noLabel _ h3)
  · rw [if_neg hm]; exact h0

theorem findLabel_none_of_noLabel (lbl : LLabel) (X : List LinstrR)
    (h : ∀ x ∈ X, isLbl x = false) : findLabel lbl X = none := by
  unfold findLabel
  rw [List.findIdx?_eq_none_iff]
  intro x hx
  cases hxl : isLabel lbl x with
  | false => rfl
  | true =>
    have := isLbl_of_isLabel lbl x hxl
    rw [h x hx] at this; exact absurd this (by simp)

theorem findLabel_none_map (lbl : LLabel) (l : List Linstr)
    (h : ∀ i ∈ l, isLbl i.li_i = false) : findLabel lbl (l.map Linstr.li_i) = none := by
  apply findLabel_none_of_noLabel
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact h i hi

theorem ctlStraightFalse (c : Linstr) (h : isCtlInstr c = true) : bodyIsStraightLine [c] = false := by
  simp only [bodyIsStraightLine, List.all_cons, List.all_nil, Bool.and_true]
  revert h; unfold isCtlInstr; cases c.li_i <;> simp

theorem bdry_cons (seg : List Linstr) (rest : List (List Linstr)) (k : Nat) :
    bdry (seg :: rest) (k + 1) = seg.length + bdry rest k := by
  simp only [bdry, List.take_succ_cons, List.flatten_cons, List.length_append]

theorem obdry_cons (seg : List Linstr) (rest : List (List Linstr)) (k : Nat) :
    obdry (seg :: rest) (k + 1) = (optSeg seg).length + obdry rest k := by
  simp only [obdry, List.take_succ_cons, List.map_cons, List.flatten_cons, List.length_append]

theorem findLabel_flatten_cons (lbl : LLabel) (seg : List Linstr) (rest : List (List Linstr)) :
    findLabel lbl ((seg :: rest).flatten.map Linstr.li_i)
      = (findLabel lbl (seg.map Linstr.li_i)).or
          ((findLabel lbl (rest.flatten.map Linstr.li_i)).map (· + seg.length)) := by
  simp only [List.flatten_cons, List.map_append, findLabel, List.findIdx?_append, List.length_map]

theorem findLabel_optflatten_cons (lbl : LLabel) (seg : List Linstr) (rest : List (List Linstr)) :
    findLabel lbl (((seg :: rest).map optSeg).flatten.map Linstr.li_i)
      = (findLabel lbl ((optSeg seg).map Linstr.li_i)).or
          ((findLabel lbl ((rest.map optSeg).flatten.map Linstr.li_i)).map (· + (optSeg seg).length)) := by
  simp only [List.map_cons, List.flatten_cons, List.map_append, findLabel, List.findIdx?_append,
    List.length_map]

theorem optSeg_findLabel_none (lbl : LLabel) (seg : List Linstr)
    (hgood : (∃ c, seg = [c] ∧ isCtlInstr c = true) ∨ bodyIsStraightLine seg = true)
    (hnone : findLabel lbl (seg.map Linstr.li_i) = none) :
    findLabel lbl ((optSeg seg).map Linstr.li_i) = none := by
  rcases hgood with ⟨c, hc, hctl⟩ | hsl
  · have hbsl : bodyIsStraightLine [c] = false := ctlStraightFalse c hctl
    rw [hc] at hnone ⊢
    simp only [optSeg, hbsl]
    exact hnone
  · rw [optSeg, if_pos hsl]
    exact findLabel_none_map lbl (optRunBody seg) (optRunBody_noLabel seg hsl)

theorem label_pres_segs (lbl : LLabel) : ∀ (segs : List (List Linstr)),
    (∀ seg ∈ segs, seg ≠ [] ∧ ((∃ c, seg = [c] ∧ isCtlInstr c = true) ∨ bodyIsStraightLine seg = true)) →
    ∀ pc, findLabel lbl (segs.flatten.map Linstr.li_i) = some pc →
      ∃ k2 pc', k2 ≤ segs.length ∧ pc + 1 = bdry segs k2 ∧
        findLabel lbl ((segs.map optSeg).flatten.map Linstr.li_i) = some pc' ∧ pc' + 1 = obdry segs k2 := by
  intro segs
  induction segs with
  | nil => intro _ pc hfl; simp [findLabel] at hfl
  | cons seg rest ih =>
    intro hgood pc hfl
    have hgoodseg := hgood seg (List.mem_cons_self ..)
    have hgoodrest : ∀ s ∈ rest, s ≠ [] ∧
        ((∃ c, s = [c] ∧ isCtlInstr c = true) ∨ bodyIsStraightLine s = true) :=
      fun s hs => hgood s (List.mem_cons_of_mem _ hs)
    rw [findLabel_flatten_cons] at hfl
    cases hseg_fl : findLabel lbl (seg.map Linstr.li_i) with
    | some p0 =>
      rw [hseg_fl] at hfl
      simp only [Option.some_or, Option.some.injEq] at hfl
      have hsingleton : ∃ c, seg = [c] ∧ isCtlInstr c = true := by
        rcases hgoodseg.2 with hc | hsl
        · exact hc
        · exfalso
          have hnn : findLabel lbl (seg.map Linstr.li_i) = none :=
            findLabel_none_map lbl seg (straightLine_noLabel seg hsl)
          rw [hnn] at hseg_fl; exact absurd hseg_fl (by simp)
      obtain ⟨c, hc, hctl⟩ := hsingleton
      have hbsl : bodyIsStraightLine [c] = false := ctlStraightFalse c hctl
      rw [hc] at hseg_fl
      simp only [List.map_cons, List.map_nil, findLabel, List.findIdx?_cons, List.findIdx?_nil,
        Option.map_none] at hseg_fl
      by_cases hlab : isLabel lbl c.li_i
      · rw [if_pos hlab] at hseg_fl
        have hp0 : p0 = 0 := (Option.some.inj hseg_fl).symm
        refine ⟨1, 0, by simp, ?_, ?_, ?_⟩
        · rw [← hfl, hp0, hc, bdry_cons]; simp [bdry]
        · rw [findLabel_optflatten_cons, hc]; simp [optSeg, hbsl, findLabel, hlab]
        · rw [obdry_cons, hc]; simp [optSeg, hbsl, obdry]
      · rw [if_neg hlab] at hseg_fl; exact absurd hseg_fl (by simp)
    | none =>
      rw [hseg_fl] at hfl
      simp only [Option.none_or] at hfl
      obtain ⟨pc_rest, hrest_fl, hpc⟩ := Option.map_eq_some_iff.mp hfl
      obtain ⟨k2r, pc'r, hk2r, hpcbr, hfl'r, hpc'br⟩ := ih hgoodrest pc_rest hrest_fl
      refine ⟨k2r + 1, pc'r + (optSeg seg).length, ?_, ?_, ?_, ?_⟩
      · simp only [List.length_cons]; omega
      · rw [bdry_cons, ← hpcbr, ← hpc]; omega
      · rw [findLabel_optflatten_cons, optSeg_findLabel_none lbl seg hgoodseg.2 hseg_fl,
          Option.none_or, hfl'r]
        simp
      · rw [obdry_cons, ← hpc'br]; omega

theorem label_pres_body (body : List Linstr) (lbl : LLabel) (pc : Nat)
    (hfl : findLabel lbl (body.map Linstr.li_i) = some pc) :
    ∃ k2 pc', k2 ≤ (splitStraightRuns body).length ∧ pc + 1 = bdry (splitStraightRuns body) k2 ∧
      findLabel lbl ((optimizeBasicBlocks body).map Linstr.li_i) = some pc' ∧
      pc' + 1 = obdry (splitStraightRuns body) k2 := by
  have hfl' : findLabel lbl ((splitStraightRuns body).flatten.map Linstr.li_i) = some pc := by
    rw [splitStraightRuns_flatten]; exact hfl
  obtain ⟨k2, pc', hk2, hpcb, hfl2, hpc'b⟩ :=
    label_pres_segs lbl (splitStraightRuns body) (splitStraightRuns_good body) pc hfl'
  exact ⟨k2, pc', hk2, hpcb, by rw [optimizeBasicBlocks_eq_optSeg]; exact hfl2, hpc'b⟩

/-- Label preservation: resolving a label in the source body and in the optimized
    body land at the start of the same basic block. -/
def LabelPres (P : Lprog) : Prop :=
  ∀ (gfn : String) (fdg : Lfundef), getFundef P gfn = some fdg →
    ∀ (lbl : LLabel) (pc : Nat), findLabel lbl (fdg.lfd_body.map Linstr.li_i) = some pc →
      ∃ (k2 pc' : Nat),
        k2 ≤ (splitStraightRuns fdg.lfd_body).length ∧
        pc + 1 = bdry (splitStraightRuns fdg.lfd_body) k2 ∧
        findLabel lbl ((optimizeBasicBlocks fdg.lfd_body).map Linstr.li_i) = some pc' ∧
        pc' + 1 = obdry (splitStraightRuns fdg.lfd_body) k2

theorem LabelPres_holds (P : Lprog) : LabelPres P :=
  fun _ fdg _ lbl pc hfl => label_pres_body fdg.lfd_body lbl pc hfl

theorem jumpSim (P : Lprog) (hlp : LabelPres P) {w} (s s' s2 : LstateP w)
    (gfn : String) (lbl : LLabel)
    (hstore : stateStore s.base = stateStore s'.base)
    (hj : evalJump P (gfn, lbl) s = some s2) :
    ∃ s2', evalJump (mapBodies optimizeBasicBlocks P) (gfn, lbl) s' = some s2' ∧ Sim P s2 s2' := by
  simp only [evalJump] at hj
  cases hg : getFundef P gfn with
  | none => rw [hg] at hj; simp at hj
  | some fdg =>
    rw [hg] at hj
    dsimp only at hj
    cases hfl : findLabel lbl (fdg.lfd_body.map Linstr.li_i) with
    | none => rw [hfl] at hj; simp at hj
    | some pc =>
      rw [hfl] at hj
      dsimp only at hj
      simp only [Option.some.injEq] at hj
      subst s2
      obtain ⟨k2, pc', hk2, hpcb, hfl', hpc'b⟩ := hlp gfn fdg hg lbl pc hfl
      refine ⟨s'.setcpc gfn (pc' + 1), ?_, ?_⟩
      · simp only [evalJump, getFundef_mapBodies, hg, Option.map_some, hfl']
      · refine ⟨fdg, k2, hg, rfl, hk2, hpcb, hpc'b, ?_⟩
        exact hstore

theorem notBranch_of_lsemStraight (is : List LinstrR) {w} (b s : Lstate w)
    (h : lsemStraight is s = some b) : ∀ i ∈ is, NotBranch i = true := by
  induction is generalizing s with
  | nil => intro i hi; simp at hi
  | cons j js ih =>
    intro i hi
    simp only [lsemStraight_cons] at h
    cases hj : lsemStep j s with
    | none => rw [hj] at h; simp at h
    | some s1 =>
      rw [hj] at h
      rcases List.mem_cons.mp hi with rfl | hmem
      · exact notBranch_of_lsemStep_some _ s s1 hj
      · exact ih s1 h i hmem

/-- **The forward simulation over fuel.** From a `Sim`-related pair, a halting
    source run is matched by a halting optimized run reaching an equal store. -/
theorem sim_main (P : Lprog) (hlp : LabelPres P) :
    ∀ (fuel : Nat) {w} (s s' t : LstateP w),
      Sim P s s' → lsemFuel P fuel s = some t →
      ∃ (fuel' : Nat) (t' : LstateP w),
        lsemFuel (mapBodies optimizeBasicBlocks P) fuel' s' = some t' ∧
        stateStore t.base = stateStore t'.base := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
    intro w s s' t hsim hfuel
    obtain ⟨fd, k, hfd, hlfn, hkle, hspc, hs'pc, hstore⟩ := hsim
    set fn := s.lfn with hfndef
    set P' := mapBodies optimizeBasicBlocks P with hP'
    set segs := splitStraightRuns fd.lfd_body with hsegdef
    have hflat : segs.flatten = fd.lfd_body := by rw [hsegdef]; exact splitStraightRuns_flatten fd.lfd_body
    have hfd' : getFundef P' fn = some { fd with lfd_body := optimizeBasicBlocks fd.lfd_body } := by
      rw [hP', getFundef_mapBodies, hfd]; rfl
    have Hfetch : ∀ (u : LstateP w), u.lfn = fn → findInstr P u = (fd.lfd_body.map Linstr.li_i)[u.base.lpc]? :=
      fun u hu => findInstr_body P fn fd hfd u hu
    have Hfetch' : ∀ (u : LstateP w), u.lfn = fn →
        findInstr P' u = ((optimizeBasicBlocks fd.lfd_body).map Linstr.li_i)[u.base.lpc]? := by
      intro u hu
      simpa using findInstr_body P' fn _ hfd' u hu
    have finish : ∀ (m : Nat), m < fuel → ∀ (s2 s2' : LstateP w),
        Sim P s2 s2' → lsemFuel P m s2 = some t →
        ∀ (pfx : Nat), (∀ rest, lsemFuel P' (pfx + rest) s' = lsemFuel P' rest s2') →
        ∃ (fuel' : Nat) (t' : LstateP w),
          lsemFuel P' fuel' s' = some t' ∧ stateStore t.base = stateStore t'.base := by
      intro m hm s2 s2' hsim2 hf2 pfx hpfx
      obtain ⟨f'', t', hf'', hst⟩ := ih m hm s2 s2' t hsim2 hf2
      exact ⟨pfx + f'', t', by rw [hpfx f'']; exact hf'', hst⟩
    by_cases hkeq : k = segs.length
    · have hbodylen : s.base.lpc = (fd.lfd_body.map Linstr.li_i).length := by
        rw [hspc, hkeq, bdry_full, hflat, List.length_map]
      have hnone : findInstr P s = none := by
        rw [Hfetch s rfl, hbodylen]; exact List.getElem?_eq_none (le_refl _)
      have ht : lsemFuel P fuel s = some s := lsemFuel_halt P fuel s hnone
      rw [ht] at hfuel
      have hst : t = s := (Option.some.inj hfuel).symm
      have hbodylen' : s'.base.lpc = ((optimizeBasicBlocks fd.lfd_body).map Linstr.li_i).length := by
        rw [hs'pc, hkeq, obdry_full, List.length_map, optimizeBasicBlocks_eq_optSeg, ← hsegdef]
      have hnone' : findInstr P' s' = none := by
        rw [Hfetch' s' hlfn, hbodylen']; exact List.getElem?_eq_none (le_refl _)
      exact ⟨0, s', lsemFuel_halt P' 0 s' hnone', by rw [hst]; exact hstore⟩
    · have hklt : k < segs.length := lt_of_le_of_ne hkle hkeq
      have hmem : segs[k] ∈ splitStraightRuns fd.lfd_body := by
        rw [← hsegdef]; exact List.getElem_mem hklt
      obtain ⟨hne, hdich⟩ := splitStraightRuns_good fd.lfd_body segs[k] hmem
      have hdecomp : fd.lfd_body.map Linstr.li_i
          = ((segs.take k).flatten).map Linstr.li_i ++ (segs[k]).map Linstr.li_i
            ++ ((segs.drop (k + 1)).flatten).map Linstr.li_i := by
        conv_lhs => rw [← hflat, flatten_decomp segs k hklt]
        simp only [List.map_append]
      have hdecomp' : (optimizeBasicBlocks fd.lfd_body).map Linstr.li_i
          = (((segs.take k).map optSeg).flatten).map Linstr.li_i
            ++ (optSeg segs[k]).map Linstr.li_i
            ++ (((segs.drop (k + 1)).map optSeg).flatten).map Linstr.li_i := by
        have hob : optimizeBasicBlocks fd.lfd_body = (segs.map optSeg).flatten := by
          rw [optimizeBasicBlocks_eq_optSeg, ← hsegdef]
        rw [hob]
        conv_lhs => rw [flatten_decomp (segs.map optSeg) k (by rw [List.length_map]; exact hklt)]
        simp only [List.map_append, List.map_take, List.map_drop, List.getElem_map]
      have hpreLen : (((segs.take k).flatten).map Linstr.li_i).length = bdry segs k := by
        simp only [bdry, List.length_map]
      have hopreLen : ((((segs.take k).map optSeg).flatten).map Linstr.li_i).length = obdry segs k := by
        simp only [obdry, List.length_map]
      have hpc_s : s.base.lpc = (((segs.take k).flatten).map Linstr.li_i).length := by
        rw [hpreLen, hspc]
      have hpc_s' : s'.base.lpc = ((((segs.take k).map optSeg).flatten).map Linstr.li_i).length := by
        rw [hopreLen, hs'pc]
      rcases hdich with ⟨c, hck, hcctl⟩ | hstraight
      · have hsegk : (segs[k]).map Linstr.li_i = [c.li_i] := by rw [hck]; rfl
        have hbsl : bodyIsStraightLine [c] = false := ctlStraightFalse c hcctl
        have hosegk : (optSeg segs[k]).map Linstr.li_i = [c.li_i] := by
          rw [hck]; simp [optSeg, hbsl]
        have hbodyc : fd.lfd_body.map Linstr.li_i
            = ((segs.take k).flatten).map Linstr.li_i ++ (c.li_i :: [])
              ++ ((segs.drop (k + 1)).flatten).map Linstr.li_i := by
          rw [hdecomp, hsegk]
        have hobodyc : (optimizeBasicBlocks fd.lfd_body).map Linstr.li_i
            = (((segs.take k).map optSeg).flatten).map Linstr.li_i ++ (c.li_i :: [])
              ++ (((segs.drop (k + 1)).map optSeg).flatten).map Linstr.li_i := by
          rw [hdecomp', hosegk]
        have hfi : findInstr P s = some c.li_i := by
          rw [Hfetch s rfl, hpc_s]; exact fetch_head _ _ [] _ c.li_i hbodyc
        have hfi' : findInstr P' s' = some c.li_i := by
          rw [Hfetch' s' hlfn, hpc_s']; exact fetch_head _ _ [] _ c.li_i hobodyc
        have hseglen1 : (segs[k]).length = 1 := by rw [hck]; rfl
        have hoptseglen1 : (optSeg segs[k]).length = 1 := by rw [hck]; simp [optSeg, hbsl]
        have hbdry1 : bdry segs (k + 1) = bdry segs k + 1 := by rw [bdry_succ segs k hklt, hseglen1]
        have hobdry1 : obdry segs (k + 1) = obdry segs k + 1 := by rw [obdry_succ segs k hklt, hoptseglen1]
        obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := by
          cases fuel with
          | zero => simp [lsemFuel, hfi] at hfuel
          | succ f => exact ⟨f, rfl⟩
        have hnextlpc : (s.nextPc).base.lpc = s.base.lpc + 1 := by simp [LstateP.nextPc, Lstate.nextPc]
        have hnextlpc' : (s'.nextPc).base.lpc = s'.base.lpc + 1 := by simp [LstateP.nextPc, Lstate.nextPc]
        have hnextstore : stateStore (s.nextPc).base = stateStore s.base := by
          simp [LstateP.nextPc, Lstate.nextPc, stateStore]
        have hnextstore' : stateStore (s'.nextPc).base = stateStore s'.base := by
          simp [LstateP.nextPc, Lstate.nextPc, stateStore]
        have simNext : Sim P s.nextPc s'.nextPc := by
          refine ⟨fd, k + 1, hfd, ?_, hklt, ?_, ?_, ?_⟩
          · show (s'.nextPc).lfn = (s.nextPc).lfn
            simp only [LstateP.nextPc]; exact hlfn
          · show (s.nextPc).base.lpc = bdry segs (k + 1)
            rw [hnextlpc, hspc, ← hbdry1]
          · show (s'.nextPc).base.lpc = obdry segs (k + 1)
            rw [hnextlpc', hs'pc, ← hobdry1]
          · show stateStore (s.nextPc).base = stateStore (s'.nextPc).base
            rw [hnextstore, hnextstore']; exact hstore
        have doStep : ∀ (s2 s2' : LstateP w),
            evalInstrP P c.li_i s = some s2 → evalInstrP P' c.li_i s' = some s2' →
            Sim P s2 s2' →
            ∃ (fuel' : Nat) (t' : LstateP w),
              lsemFuel P' fuel' s' = some t' ∧ stateStore t.base = stateStore t'.base := by
          intro s2 s2' hstep hstep' hsim2
          have hf2 : lsemFuel P f s2 = some t := by
            have := hfuel
            simp only [lsemFuel, hfi, hstep] at this
            exact this
          have hpfx : ∀ rest, lsemFuel P' (1 + rest) s' = lsemFuel P' rest s2' := by
            intro rest
            rw [Nat.add_comm]
            simp only [lsemFuel, hfi', hstep']
          exact finish f (by omega) s2 s2' hsim2 hf2 1 hpfx
        have hcases :
            (∃ lk ll, c.li_i = .Llabel lk ll) ∨ (∃ d, c.li_i = .Lgoto d)
              ∨ (∃ d, c.li_i = .Ligoto d) ∨ (∃ cond lbl, c.li_i = .Lcond cond lbl)
              ∨ c.li_i = .Lret := by
          revert hcctl; unfold isCtlInstr; cases c.li_i <;> simp
        rcases hcases with ⟨lk, ll, hcli⟩ | ⟨d, hcli⟩ | ⟨d, hcli⟩ | ⟨cond, lbl, hcli⟩ | hcli
        · refine doStep s.nextPc s'.nextPc ?_ ?_ simNext
          · rw [hcli]; simp [evalInstrP, lsemStep, LstateP.nextPc]
          · rw [hcli]; simp [evalInstrP, lsemStep, LstateP.nextPc]
        · have hf := hfuel
          simp only [lsemFuel, hfi, hcli, evalInstrP] at hf
          cases hj : evalJump P d s with
          | none => rw [hj] at hf; simp at hf
          | some s2src =>
            obtain ⟨s2', hj', hsim2⟩ := jumpSim P hlp s s' s2src d.1 d.2 hstore hj
            refine doStep s2src s2' ?_ ?_ hsim2
            · rw [hcli]; exact hj
            · rw [hcli]; exact hj'
        · simp [lsemFuel, hfi, hcli, evalInstrP] at hfuel
        · by_cases hcnd : evalOperand s.base cond ≠ 0
          · have hf := hfuel
            simp only [lsemFuel, hfi, hcli, evalInstrP, if_pos hcnd] at hf
            cases hj : evalJump P (s.lfn, lbl) s with
            | none => rw [hj] at hf; simp at hf
            | some s2src =>
              obtain ⟨s2', hj', hsim2⟩ := jumpSim P hlp s s' s2src s.lfn lbl hstore hj
              refine doStep s2src s2' ?_ ?_ hsim2
              · rw [hcli]; simp only [evalInstrP, if_pos hcnd]; exact hj
              · have hcnd' : evalOperand s'.base cond ≠ 0 := by
                  rw [← evalOperand_congr hstore cond]; exact hcnd
                rw [hcli]; simp only [evalInstrP, if_pos hcnd']; rw [hlfn]; exact hj'
          · have hcnd' : ¬ evalOperand s'.base cond ≠ 0 := by
              rw [← evalOperand_congr hstore cond]; exact hcnd
            refine doStep s.nextPc s'.nextPc ?_ ?_ simNext
            · rw [hcli]; simp only [evalInstrP, if_neg hcnd]
            · rw [hcli]; simp only [evalInstrP, if_neg hcnd']
        · simp [lsemFuel, hfi, hcli, evalInstrP] at hfuel
      · have hnb : ∀ i ∈ (segs[k]).map Linstr.li_i, NotBranch i = true :=
          fun i hi => notBranch_of_straight segs[k] hstraight i hi
        obtain ⟨b, hstr, hlefuel, htail⟩ :=
          fuelRun P fn (fd.lfd_body.map Linstr.li_i) Hfetch ((segs[k]).map Linstr.li_i) hnb
            (((segs.take k).flatten).map Linstr.li_i) (((segs.drop (k + 1)).flatten).map Linstr.li_i)
            hdecomp s rfl hpc_s fuel t hfuel
        have hoptseg : optSeg segs[k] = optRunBody segs[k] := by simp [optSeg, hstraight]
        have hmap : Option.map stateStore (lsemStraight ((optSeg segs[k]).map Linstr.li_i) s'.base)
            = some (stateStore b) := by
          have h1 : Option.map stateStore (lsemStraight ((optSeg segs[k]).map Linstr.li_i) s'.base)
              = Option.map stateStore (lsemStraight ((segs[k]).map Linstr.li_i) s'.base) := by
            rw [hoptseg, optRunBody_stateStore]
          have h2 : Option.map stateStore (lsemStraight ((segs[k]).map Linstr.li_i) s'.base)
              = Option.map stateStore (lsemStraight ((segs[k]).map Linstr.li_i) s.base) :=
            lsemStraight_stateStore _ hstore.symm
          rw [h1, h2, hstr]; rfl
        obtain ⟨b_opt, hbopt, hbopt_store⟩ :
            ∃ b_opt, lsemStraight ((optSeg segs[k]).map Linstr.li_i) s'.base = some b_opt
              ∧ stateStore b_opt = stateStore b := by
          cases hlo : lsemStraight ((optSeg segs[k]).map Linstr.li_i) s'.base with
          | none => rw [hlo] at hmap; simp at hmap
          | some b_opt => rw [hlo] at hmap; exact ⟨b_opt, rfl, Option.some.inj hmap⟩
        have hnb' : ∀ i ∈ (optSeg segs[k]).map Linstr.li_i, NotBranch i = true :=
          notBranch_of_lsemStraight _ b_opt s'.base hbopt
        have hfwd := runForward P' fn ((optimizeBasicBlocks fd.lfd_body).map Linstr.li_i) Hfetch'
          ((optSeg segs[k]).map Linstr.li_i) hnb'
          ((((segs.take k).map optSeg).flatten).map Linstr.li_i)
          ((((segs.drop (k + 1)).map optSeg).flatten).map Linstr.li_i)
          hdecomp' s' hlfn hpc_s' b_opt hbopt
        have hsim2 : Sim P ⟨{ b with lpc := (((segs.take k).flatten).map Linstr.li_i).length + ((segs[k]).map Linstr.li_i).length }, fn⟩
                          ⟨{ b_opt with lpc := ((((segs.take k).map optSeg).flatten).map Linstr.li_i).length + ((optSeg segs[k]).map Linstr.li_i).length }, fn⟩ := by
          refine ⟨fd, k + 1, hfd, rfl, hklt, ?_, ?_, ?_⟩
          · show (((segs.take k).flatten).map Linstr.li_i).length + ((segs[k]).map Linstr.li_i).length
                = bdry segs (k + 1)
            rw [bdry_succ segs k hklt, hpreLen, List.length_map]
          · show ((((segs.take k).map optSeg).flatten).map Linstr.li_i).length + ((optSeg segs[k]).map Linstr.li_i).length
                = obdry segs (k + 1)
            rw [obdry_succ segs k hklt, hopreLen, List.length_map]
          · exact hbopt_store.symm
        have hpos : 0 < ((segs[k]).map Linstr.li_i).length := by
          rw [List.length_map]
          rcases hh : segs[k] with _ | ⟨a, as⟩
          · exact absurd hh hne
          · simp
        have hm : fuel - ((segs[k]).map Linstr.li_i).length < fuel :=
          Nat.sub_lt (lt_of_lt_of_le hpos hlefuel) hpos
        exact finish _ hm _ _ hsim2 htail _ hfwd

/-- The entry-point `Sim`: a state at a function's pc 0 relates to itself. -/
theorem Sim_entry (P : Lprog) {w} (s : LstateP w) (fd : Lfundef)
    (hfd : getFundef P s.lfn = some fd) (hpc : s.base.lpc = 0) : Sim P s s :=
  ⟨fd, 0, hfd, rfl, Nat.zero_le _, by simp [bdry, hpc], by simp [obdry, hpc], rfl⟩

/-- `lsem`-level store-image preservation of `mapBodies optimizeBasicBlocks` from
    any `Sim`-related start. -/
theorem lsem_store_preserved (P : Lprog) {w} (s s' t : LstateP w)
    (hsim : Sim P s s') (h : lsem P s t) :
    ∃ t', lsem (mapBodies optimizeBasicBlocks P) s' t' ∧ stateStore t.base = stateStore t'.base := by
  obtain ⟨fuel, hfuel⟩ := h
  obtain ⟨fuel', t', hf', hst⟩ := sim_main P (LabelPres_holds P) fuel s s' t hsim hfuel
  exact ⟨t', ⟨fuel', hf'⟩, hst⟩

/-- **Full-CFG store preservation for `mapBodies optimizeBasicBlocks`.** Running a
    program from a function entry (pc 0) and running the basic-block-optimized
    program from the same entry state reach the same store, over the labeled,
    program-counter-indexed `lsem`. -/
theorem mapBodies_entry_store_preserved (P : Lprog) {w} (s t : LstateP w) (fd : Lfundef)
    (hfd : getFundef P s.lfn = some fd) (hpc : s.base.lpc = 0) (h : lsem P s t) :
    ∃ t', lsem (mapBodies optimizeBasicBlocks P) s t' ∧ stateStore t.base = stateStore t'.base :=
  lsem_store_preserved P s s t (Sim_entry P s fd hfd hpc) h

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)

/-- Optimize every function body's basic blocks: `optimizeBasicBlocks` on each
    body, mapped over the whole program (`mapBodies optimizeBasicBlocks`). -/
def optimizeLprogBasicBlocks (p : Lprog) : Lprog := mapBodies optimizeBasicBlocks p

/-- **The one optimizing compiler back-end.** Every owned emit driver renders its
    `Lprog` through this entry point: `optimizeLprogBasicBlocks` — the four
    verified passes (reload/spill elimination, instruction scheduling, load-CSE)
    on each maximal straight-line run of every function body, with control-flow
    instructions kept verbatim — followed by the pure printer `renderLprogAtt`.
    The full-control-flow-graph soundness is `mapBodies_entry_store_preserved`:
    over the labeled, program-counter-indexed semantics `JasminLsemLabeled.lsem`,
    running the optimized program from a function entry reaches the same register
    map and memory as the source. This optimizes a loop body — a straight-line run
    between labels and jumps — with a proven guarantee, where the earlier
    per-function guard left any control-flow body unoptimized. The `.jazz` text
    path (`JasminPrint.emitJazz`) is the jasminc-comparison/interop side and does
    NOT go through this. -/
def renderOwned (p : Lprog) : String := renderLprogAtt (optimizeLprogBasicBlocks p)

/-- **The owned back end with the frame cleared before every return.**
    `StackZeroize.zeroizeLprog` runs after `optimizeLprogBasicBlocks` and before
    the printer, so the census `StackZeroize.writtenFrameCells` reads the body
    that is printed, and the reload and spill elimination of the optimizer never
    sees a zero store to remove. The stores go between a body's last instruction
    and its `Lret`, which the printer renders as the frame teardown and the
    return, so they land after the callee-saved restores and while the frame is
    still addressed by `RSP`.

    `StackZeroize.zeroizeBody_lsemRun_erases` gives the effect on the frame and
    `StackZeroize.zeroizePrefix_preserves_nonFrame` what is left alone; a body
    that does not end in `Lret` is returned unchanged. An emitter whose kernel
    holds a secret in its frame composes this in place of `renderOwned`. -/
def renderOwnedZeroized (p : Lprog) : String :=
  renderLprogAtt (StackZeroize.zeroizeLprog (optimizeLprogBasicBlocks p))

/-- Fold a use-once ABI memory load into its single vector consumer: a
    `VMOVDQU [kv.d] [mem.m]` whose spill `d` is defined once (this load) and read
    once is deleted, and its consumer's `kv.d` source is rewritten to the memory
    operand `mem.m`. The ABI inputs (`mem.RSI`/`mem.RDI`) are read-only in the body,
    so the value is stable between the load and the use; the VEX packed ALU takes a
    memory source in its first slot (the printer places it there). This removes the
    load, the induced `kv.N` spill, and the mem→mem bounce for each round constant. -/
def foldAbiLoadBody (body : Lcmd) : Lcmd :=
  let srcRegs : Linstr → List String := fun i =>
    match i.li_i with
    | .Lopn _ _ srcs => srcs.filterMap (fun o => match o with | .reg n => some n | _ => none)
    | _ => []
  let dstRegs : Linstr → List String := fun i =>
    match i.li_i with
    | .Lopn dsts _ _ => dsts.filterMap (fun o => match o with | .reg n => some n | _ => none)
    | _ => []
  let allSrc := body.flatMap srcRegs
  let allDst := body.flatMap dstRegs
  let useCount := fun nm => (allSrc.filter (· == nm)).length
  let defCount := fun nm => (allDst.filter (· == nm)).length
  let foldMap : List (String × String) := body.filterMap (fun i =>
    match i.li_i with
    | .Lopn [.reg d] "VMOVDQU" [.reg m] =>
        if "kv.".isPrefixOf d && "mem.".isPrefixOf m
           && defCount d == 1 && useCount d == 1 then some (d, m) else none
    | _ => none)
  let foldNames := foldMap.map Prod.fst
  body.filterMap (fun i =>
    match i.li_i with
    | .Lopn [.reg d] "VMOVDQU" [.reg _] =>
        if foldNames.contains d then none else some i
    | .Lopn dsts opn srcs =>
        let srcs' := srcs.map (fun o =>
          match o with
          | .reg n => match foldMap.find? (fun p => p.1 == n) with
                      | some (_, m) => LOperand.reg m
                      | none => o
          | _ => o)
        some ⟨i.li_ii, .Lopn dsts opn srcs'⟩
    | _ => some i)

/-- `foldAbiLoadBody` over every function body of an `Lprog`. -/
def foldAbiLoad (p : Lprog) : Lprog :=
  { p with lp_funcs := p.lp_funcs.map (fun (n, f) =>
      (n, { f with lfd_body := foldAbiLoadBody f.lfd_body })) }

/-- `renderOwned` for a body whose RA reserved `%ymm15` (the batch8 SoA path via
    `comToLfundefPhysAbiFromVirt (reserveVecScratch := true)`): folds use-once ABI
    loads into their consumers, then omits the per-op `%ymm15` save/reload in the
    vector-spill legalization, since the register is provably free. Identical to
    `renderOwned` for every other body. -/
def renderOwnedReserveVecScratch (p : Lprog) : String :=
  renderLprogAtt (optimizeLprogBasicBlocks (foldAbiLoad p)) none true

/-! ## The `Com` stage ahead of the exporter

`ownedComStage` is the `Com → Com` pass that an owned emitter applies before
`Com.toLprogPhysAbi`. Its one pass is the range-driven fold
`Optimizer.ComRangeFold.comRangeOpt`, selected by the input intervals: `none` (the
default) leaves the program unchanged (`ownedComStage_none`), and `some ivs` folds the
bindings the intervals of `ivs` settle and removes the copies and dead bindings, in time
linear in the size of the program. `ownedComStage_denote` is its soundness: the program
handed to the exporter denotes what the source denotes on every valuation whose register
inputs lie in their intervals. `renderOwnedCom` is the whole owned back end from a `Com`:
the stage, the exporter and `renderOwned`. -/

section ComStage

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.RangeDomain (Iv)
open CatCrypt.Crypto.Optimizer.ComRangeFold (comRangeOpt comRangeOpt_denote InputsIn)

/-- The `Com → Com` stage before the exporter: the range fold under the input intervals
    `rangeIvs?`, or the identity for `none`. -/
def ownedComStage {Γ : Ctxt jasminDialect} {t : JasminTy}
    (rangeIvs? : Option (HVector (fun _ => Iv) Γ)) (com : Com jasminDialect Γ t) :
    Com jasminDialect Γ t :=
  comRangeOpt rangeIvs? com

theorem ownedComStage_none {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) : ownedComStage none com = com := rfl

/-- **Soundness of the `Com` stage**: on a valuation whose register inputs lie in the
    selected intervals, the program handed to the exporter denotes what `com` denotes. -/
theorem ownedComStage_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (rangeIvs? : Option (HVector (fun _ => Iv) Γ)) (com : Com jasminDialect Γ t)
    (V : Ctxt.Valuation Γ) (h : ∀ ivs, rangeIvs? = some ivs → InputsIn ivs V) :
    (ownedComStage rangeIvs? com).denote V = com.denote V :=
  comRangeOpt_denote rangeIvs? com V h

/-- **The owned back end from a `Com`**: `ownedComStage`, then `Com.toLprogPhysAbi` with
    the given ABI maps, then `renderOwned`. With `rangeIvs? = none` it is
    `renderOwned (Com.toLprogPhysAbi com …)` (`renderOwnedCom_none`). -/
def renderOwnedCom {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (rangeIvs? : Option (HVector (fun _ => Iv) Γ) := none)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (inLoadMap : InLoadMap := fun _ => none)
    (outStoreMap : OutStoreMap := [])
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64])
    (residence : Option (Array Nat) := none)
    (abiW : Nat := 0)
    (forceLivePin : Bool := false) : String :=
  renderOwned (Com.toLprogPhysAbi (ownedComStage rangeIvs? com) fname shiftImm immSlotMap
    inLoadMap outStoreMap abiArgs abiTyin residence abiW forceLivePin)

theorem renderOwnedCom_none {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) (shiftImm : ShiftImmOracle)
    (immSlotMap : ImmSlotMap) (inLoadMap : InLoadMap) (outStoreMap : OutStoreMap)
    (abiArgs : List String) (abiTyin : List Nat) (residence : Option (Array Nat))
    (abiW : Nat) (forceLivePin : Bool) :
    renderOwnedCom com fname none shiftImm immSlotMap inLoadMap outStoreMap abiArgs abiTyin
        residence abiW forceLivePin =
      renderOwned (Com.toLprogPhysAbi com fname shiftImm immSlotMap inLoadMap outStoreMap
        abiArgs abiTyin residence abiW forceLivePin) := rfl

end ComStage

end CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
