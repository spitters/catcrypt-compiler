/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.SpeculativeCTControlFlow
public import CatCrypt.Crypto.SecureCompilation.X86Backend.SpeculativeCTControlFlow

/-!
# Recognising the emitted counted-loop and branch frames as `OwnedCF`

`MachineConstantTime.OwnedCF` is the structured control-flow model over
straight-line `List (JInstr 64)` leaves: sequential composition, a counted loop
with a compile-time trip count, and a conditional on a register guard. An
emitted `Lcmd` carries control flow as `Llabel`/`Lgoto`/`Lcond` instructions
instead. This module is the partial recogniser between the two.

`lcmdToOwnedCF` parses an `Lcmd` into an `OwnedCF 64` when the command is built
from the frames the exporters emit, and returns `none` otherwise.

## The two recognised frames

The **static counted loop** is the frame `JasminLprogExport.forLoopLcmd` and
`forLoopLcmdN` emit and `LprogControlFlow.loopLcmd` wraps:

```
    MOV  ctr, #n                -- counter seed, a compile-time immediate
  .L<top>:
    <body>                      -- straight-line
    SUB  ctr, #1                -- counter decrement
    CMP  ctr, #0                -- flag materialisation
    Lcond cc → .L<top>          -- back-edge
```

It maps to `OwnedCF.loop n` over the gathered body. The counter seed is read off
the last instruction of the preceding straight-line run, so the trip count `n`
is the program's literal; a seed that is not an immediate is not recognised.

The **forward conditional** is the frame `FrontControlLsem.ifLR` describes:

```
    Lcond guard → .Lthen
    <else block>                -- straight-line
    Lgoto .Lend
  .Lthen:
    <then block>                -- straight-line
  .Lend:
```

It maps to `OwnedCF.ifPub guard`, with the fall-through block as the `else` arm
and the jump target as the `then` arm, matching `cfExec`'s reading of the guard
(`= 0` selects the `else` arm). `guard` must name a general-purpose register:
a guard naming a condition code (`NZ`, `Z`, …) is not recognised, because
`cfExec` reads `JState.get guard` from the register file and no `JInstr` writes
a condition code.

## The flag-only compares

`JInstr` has no compare instruction, so a `CMP`/`TEST` whose destination is its
own first source has no image in a straight-line leaf. The recogniser drops
those instructions from the leaves it gathers: the counter test of a loop frame,
and the `CMP ctr, invBase` liveness touches `forLoopLcmdN` appends. Both
operands of a dropped instruction are a register or an immediate, so a dropped
instruction touches no memory and contributes no `MLeak`.

## Scope

Recognised: nested and sequenced static counted loops, GP-register-guarded
forward conditionals, and straight-line runs, in any composition.

Not recognised, and with no `OwnedCF` image:

* a runtime trip count — `forLoopLcmdNRt`, `whileLcmdNz`,
  `forLoopLcmdNRtNested` and `blockLoopFrame` seed the counter from an operand
  (`MOV Lctr, countOp`), while `OwnedCF.loop` carries a `Nat`;
* the zero-trip top guard `CMP ctr,#0 ; Lcond Z → .Lend … .Lend:` those four
  exporters wrap the loop in, whose guard is a condition code;
* the forward skip `QuerySampleBranchFront.condSkip` emits
  (`CMP g,#imm ; Lcond cc → lbl ; <then> ; lbl:`), whose guard is a condition
  code;
* `Lcall`, `Ligoto`, `Lsyscall`, `LstoreLabel` and external labels.

## The result

`lcmdToOwnedCF_cfAllDirect` carries the addressing class across the recogniser:
an `Lcmd` in which no operand is register-indexed (`lcmdDirect`) recognises to
an `OwnedCF` every leaf of which is index-free (`CFAllDirect`), which is the
hypothesis of `SpeculativeCTControlFlow.cfSpecExec_arch_mem_cfAddrs`.

Execution agreement between `cfExec` on the recognised block and the emitted
command's own semantics is not established here. It needs two things this stack
does not carry: a flag model on the `Lstate` side (`JasminLsem.applyOpn "CMP"`
is `none`, and `Lstate` has no flag component), and the identification of the
back-edge's condition operand with the counter register — `forLoopLcmd*` emit
`Lcond (.reg "NZ") top` while the counter is `Lctr<d>`, whereas
`JasminLsemLoop.loopLR` runs the back-edge by naming the counter register
`"NZ"` (`loopLR_eq_loopLcmd_dropCmp`). With those, the statement to prove is that
`lsemFuel` on the emitted frame reaches the state `GatherLsemTie.LJCorr`-related
to `(cfExec s cf).2`, and that its `lsemLeak` is the image of `(cfExec s cf).1`.
The straight-line case of that statement is
`GatherLsemTie.gatherJBlock6_lsem_agree`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdToOwnedCF

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr JState)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime (OwnedCF IsDirect)
open CatCrypt.Crypto.SecureCompilation.X86Backend.SpeculativeCTControlFlow
  (CFAllDirect cfSpecExec cfAddrs CFPredictor SLeak)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage (allDirect)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCTPreservation
  (linstrRDirect lcmdDirect lcmdDirect_iff lowerCov6_direct mapM_flatten_direct)
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms (lowerCov6L)
open CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrGatherExtended (isLret)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
  (frameSize bodyIsU64 qsaveBytes qsaveBytesFor)

/-! ## 1. Instruction classes -/

/-- A register or immediate operand. -/
def regOrImm : LOperand → Bool
  | .reg _ => true
  | .imm _ => true
  | _ => false

/-- The width-tagged spellings of `MOV` the exporters emit for a counter seed. -/
def isMovMnem (m : String) : Bool := m == "MOV" || m == "MOV:64" || m == "MOVQ"

/-- The width-tagged spellings of `SUB`. -/
def isSubMnem (m : String) : Bool := m == "SUB" || m == "SUB:64"

/-- The width-tagged spellings of the flag-only compares. -/
def isCmpMnem (m : String) : Bool :=
  m == "CMP" || m == "CMP:64" || m == "TEST" || m == "TEST:64"

/-- The condition-code names a `Lcond` operand carries when it reads a flag
    rather than a general-purpose register. -/
def isCondCode (r : String) : Bool :=
  r == "NZ" || r == "Z" || r == "NE" || r == "E" || r == "C" || r == "NC" ||
    r == "B" || r == "NB" || r == "A" || r == "AE" || r == "BE" || r == "G" ||
    r == "GE" || r == "L" || r == "LE" || r == "S" || r == "NS" || r == "O" ||
    r == "NO" || r == "P" || r == "NP"

/-- An instruction that transfers no control and declares no label. -/
def isStraightR : LinstrR → Bool
  | .Lopn _ _ _ => true
  | .Lalign => true
  | _ => false

/-- `isStraightR` on a positioned instruction. -/
def isStraightL (i : Linstr) : Bool := isStraightR i.li_i

/-- A compare that writes only the flags: a `CMP`/`TEST` whose destination is its
    own first source, over register or immediate operands. -/
def isFlagOnly (i : Linstr) : Bool :=
  match i.li_i with
  | .Lopn [.reg d] m [.reg s, o] => isCmpMnem m && d == s && regOrImm o
  | _ => false

/-- The counter register and compile-time trip count of a loop seed
    `MOV ctr, #n`. -/
def counterSeed? (i : Linstr) : Option (String × Nat) :=
  match i.li_i with
  | .Lopn [.reg d] m [.imm n] => if isMovMnem m then some (d, n) else none
  | _ => none

/-- The counter decrement `SUB ctr, #1` of a loop frame. -/
def isCounterDec (ctr : String) (i : Linstr) : Bool :=
  match i.li_i with
  | .Lopn [.reg d] m [.reg s, .imm 1] => isSubMnem m && d == ctr && s == ctr
  | _ => false

/-- The counter test `CMP ctr, #0` of a loop frame. -/
def isCounterTest (ctr : String) (i : Linstr) : Bool :=
  match i.li_i with
  | .Lopn [.reg d] m [.reg s, .imm 0] => isCmpMnem m && d == ctr && s == ctr
  | _ => false

/-- The back-edge `Lcond cc → top` of a loop frame. -/
def isBackEdge (top : LLabel) (i : Linstr) : Bool :=
  match i.li_i with
  | .Lcond (.reg cc) l => isCondCode cc && l == top
  | _ => false

/-- The region between a loop frame's label and its back-edge is a loop body: it
    transfers no control, it ends with the counter test, and it decrements the
    counter. -/
def loopFrameOk (ctr : String) (region : Lcmd) : Bool :=
  region.all isStraightL
    && (match region.getLast? with
        | some i => isCounterTest ctr i
        | none => false)
    && region.any (isCounterDec ctr)

/-! ## 2. The control-flow skeleton -/

/-- The control-flow skeleton of an `Lcmd`: the four `OwnedCF` shapes with
    straight-line `Lcmd` segments at the leaves. -/
inductive LcmdCF where
  /-- A straight-line segment. -/
  | straight (seg : Lcmd)
  /-- Sequential composition. -/
  | seq (a b : LcmdCF)
  /-- A counted loop with a compile-time trip count. -/
  | loop (n : Nat) (body : LcmdCF)
  /-- A conditional on a general-purpose register. -/
  | ifPub (guard : String) (thenB elseB : LcmdCF)

/-- The trip counts of the counted loops of a skeleton, in order. -/
def LcmdCF.loopCounts : LcmdCF → List Nat
  | .straight _ => []
  | .seq a b => a.loopCounts ++ b.loopCounts
  | .loop n b => n :: b.loopCounts
  | .ifPub _ t e => t.loopCounts ++ e.loopCounts

/-- Parse an `Lcmd` into a control-flow skeleton, consuming one frame per unit of
    `fuel`. A straight-line run followed by nothing is a leaf; a straight-line run
    followed by an internal label whose preceding instruction seeds a counter with
    a positive immediate and whose region closes with the counter test and a
    back-edge is a counted loop; a straight-line run followed by a conditional on a
    general-purpose register laid out as `Lcond ; else ; Lgoto ; .Lthen: ; then ;
    .Lend:` is a conditional. Everything else is `none`. -/
def parseLcmdCF : Nat → Lcmd → Option LcmdCF
  | 0, _ => none
  | fuel + 1, c =>
      match c.dropWhile isStraightL with
      | [] => some (.straight (c.takeWhile isStraightL))
      | i :: rest =>
          match i.li_i with
          | .Llabel .internal top =>
              match (c.takeWhile isStraightL).getLast?.bind counterSeed? with
              | none => none
              | some (ctr, n) =>
                  if 0 < n then
                    match rest.dropWhile (fun j => !isBackEdge top j) with
                    | [] => none
                    | _ :: after =>
                        if loopFrameOk ctr (rest.takeWhile (fun j => !isBackEdge top j)) then
                          (parseLcmdCF fuel after).map (fun k =>
                            .seq (.straight (c.takeWhile isStraightL))
                              (.seq (.loop n
                                (.straight (rest.takeWhile (fun j => !isBackEdge top j)))) k))
                        else none
                  else none
          | .Lcond (.reg guard) lThen =>
              if isCondCode guard then none
              else
                match rest.dropWhile isStraightL with
                | j :: k :: rest2 =>
                    match j.li_i, k.li_i with
                    | .Lgoto (_, lEnd), .Llabel .internal lThen' =>
                        if lThen' == lThen && lEnd != lThen then
                          match rest2.dropWhile isStraightL with
                          | [] => none
                          | m :: after =>
                              match m.li_i with
                              | .Llabel .internal lEnd' =>
                                  if lEnd' == lEnd then
                                    (parseLcmdCF fuel after).map (fun r =>
                                      .seq (.straight (c.takeWhile isStraightL))
                                        (.seq (.ifPub guard
                                          (.straight (rest2.takeWhile isStraightL))
                                          (.straight (rest.takeWhile isStraightL))) r))
                                  else none
                              | _ => none
                        else none
                    | _, _ => none
                | _ => none
          | _ => none

/-! ## 3. Gathering the leaves -/

/-- Gather one straight-line segment to a `JInstr` block, dropping the flag-only
    compares. The frame size and spill width are the ones
    `GatherImmForms.gatherJBlock6` computes for the whole body. -/
def gatherSeg (frame spillW : Nat) (seg : Lcmd)
    (qsaveB : Nat := qsaveBytes) : Option (List (JInstr 64)) :=
  ((seg.filter (fun i => !isFlagOnly i)).mapM
    (fun i => lowerCov6L frame spillW i qsaveB)).map List.flatten

/-- Gather every leaf of a skeleton. -/
def lcmdCFToOwnedCF (frame spillW qsaveB : Nat) : LcmdCF → Option (OwnedCF 64)
  | .straight seg => (gatherSeg frame spillW seg qsaveB).map OwnedCF.straight
  | .seq a b =>
      match lcmdCFToOwnedCF frame spillW qsaveB a, lcmdCFToOwnedCF frame spillW qsaveB b with
      | some x, some y => some (.seq x y)
      | _, _ => none
  | .loop n b => (lcmdCFToOwnedCF frame spillW qsaveB b).map (OwnedCF.loop n)
  | .ifPub g t e =>
      match lcmdCFToOwnedCF frame spillW qsaveB t, lcmdCFToOwnedCF frame spillW qsaveB e with
      | some x, some y => some (.ifPub g x y)
      | _, _ => none

/-- **The recogniser.** Parse an emitted `Lcmd` into the structured control-flow
    block it is, and gather each straight-line leaf into a `JInstr` block. The
    trailing `Lret` is dropped and the frame size and spill width are computed
    exactly as `GatherImmForms.gatherJBlock6` computes them. `none` for a command
    outside the recognised frames. -/
def lcmdToOwnedCF (body : Lcmd) : Option (OwnedCF 64) :=
  (parseLcmdCF (body.length + 1) (body.filter (fun i => !isLret i))).bind
    (lcmdCFToOwnedCF (frameSize body) (if bodyIsU64 body then 64 else 32)
      (qsaveBytesFor body))

/-! ## 4. The addressing class crosses the recogniser -/

/-- Every instruction of every leaf of a skeleton is index-free. -/
def LcmdCFDirect : LcmdCF → Prop
  | .straight seg => ∀ i ∈ seg, linstrRDirect i.li_i = true
  | .seq a b => LcmdCFDirect a ∧ LcmdCFDirect b
  | .loop _ b => LcmdCFDirect b
  | .ifPub _ t e => LcmdCFDirect t ∧ LcmdCFDirect e

/-- Index-freeness passes to a sublist. -/
theorem direct_sublist {c d : Lcmd} (hs : d.Sublist c)
    (hd : ∀ i ∈ c, linstrRDirect i.li_i = true) :
    ∀ i ∈ d, linstrRDirect i.li_i = true :=
  fun i hi => hd i (hs.mem hi)

/-- A member of a `takeWhile` prefix is a member of the list. -/
theorem mem_of_mem_takeWhile' {α : Type} {p : α → Bool} {l : List α} {x : α}
    (h : x ∈ l.takeWhile p) : x ∈ l := (List.takeWhile_sublist _).mem h

/-- A member of the tail of a `dropWhile` suffix is a member of the list. -/
theorem mem_of_mem_tail_dropWhile {α : Type} {p : α → Bool} {l t : List α} {a x : α}
    (heq : l.dropWhile p = a :: t) (hx : x ∈ t) : x ∈ l :=
  (List.dropWhile_sublist _).mem (by rw [heq]; exact List.mem_cons_of_mem a hx)

/-- A member of the second tail of a `dropWhile` suffix is a member of the list. -/
theorem mem_of_mem_tail2_dropWhile {α : Type} {p : α → Bool} {l t : List α} {a b x : α}
    (heq : l.dropWhile p = a :: b :: t) (hx : x ∈ t) : x ∈ l :=
  (List.dropWhile_sublist _).mem
    (by rw [heq]; exact List.mem_cons_of_mem a (List.mem_cons_of_mem b hx))

/-- The gather of an index-free segment is in the constant-time addressing class:
    the dropped flag-only compares are removed by a filter, and every remaining
    instruction lowers to direct instructions by `lowerCov6_direct`. -/
theorem gatherSeg_allDirect {frame spillW qsaveB : Nat} {seg : Lcmd}
    {g : List (JInstr 64)}
    (hd : ∀ i ∈ seg, linstrRDirect i.li_i = true)
    (h : gatherSeg frame spillW seg qsaveB = some g) : allDirect g = true := by
  simp only [gatherSeg, Option.map_eq_some_iff] at h
  obtain ⟨ls, hls, rfl⟩ := h
  refine mapM_flatten_direct ?_ _ ?_ ls hls
  · intro i _ js hj
    exact lowerCov6_direct ‹_› hj
  · intro i hi
    exact hd i (List.mem_of_mem_filter hi)

/-- A gathered skeleton whose leaves are index-free is an index-free structured
    block. -/
theorem lcmdCFToOwnedCF_cfAllDirect {frame spillW qsaveB : Nat} :
    ∀ (k : LcmdCF) (cf : OwnedCF 64), LcmdCFDirect k →
      lcmdCFToOwnedCF frame spillW qsaveB k = some cf → CFAllDirect cf := by
  intro k
  induction k with
  | straight seg =>
    intro cf hd h
    simp only [lcmdCFToOwnedCF, Option.map_eq_some_iff] at h
    obtain ⟨g, hg, rfl⟩ := h
    exact ConstantTimeCoverage.allDirect_mem_isDirect g (gatherSeg_allDirect hd hg)
  | seq a b iha ihb =>
    intro cf hd h
    simp only [lcmdCFToOwnedCF] at h
    split at h
    · rename_i x y hx hy
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨iha x hd.1 hx, ihb y hd.2 hy⟩
    · exact absurd h (by simp)
  | loop n b ihb =>
    intro cf hd h
    simp only [lcmdCFToOwnedCF, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, rfl⟩ := h
    exact ihb x hd hx
  | ifPub g t e iht ihe =>
    intro cf hd h
    simp only [lcmdCFToOwnedCF] at h
    split at h
    · rename_i x y hx hy
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨iht x hd.1 hx, ihe y hd.2 hy⟩
    · exact absurd h (by simp)

/-- The parse keeps every leaf inside the command it parses, so index-freeness of
    the command is index-freeness of every leaf. -/
theorem parseLcmdCF_direct :
    ∀ (fuel : Nat) (c : Lcmd) (k : LcmdCF),
      (∀ i ∈ c, linstrRDirect i.li_i = true) → parseLcmdCF fuel c = some k →
      LcmdCFDirect k := by
  intro fuel
  induction fuel with
  | zero => intro c k _ h; exact absurd h (by simp [parseLcmdCF])
  | succ f ih =>
    intro c k hd h
    have hpre : ∀ i ∈ c.takeWhile isStraightL, linstrRDirect i.li_i = true :=
      direct_sublist (List.takeWhile_sublist _) hd
    have hdrop : ∀ i ∈ c.dropWhile isStraightL, linstrRDirect i.li_i = true :=
      direct_sublist (List.dropWhile_sublist _) hd
    rw [parseLcmdCF] at h
    split at h
    · -- no control instruction: a single straight-line leaf
      simp only [Option.some.injEq] at h
      subst h
      exact hpre
    · rename_i i rest hsplit
      have hrest : ∀ j ∈ rest, linstrRDirect j.li_i = true := fun j hj =>
        hdrop j (by rw [hsplit]; exact List.mem_cons_of_mem i hj)
      split at h
      · -- counted loop
        split at h
        · exact absurd h (by simp)
        · rename_i ctr n _
          split at h
          · split at h
            · exact absurd h (by simp)
            · rename_i after heqd
              have hafter : ∀ j ∈ after, linstrRDirect j.li_i = true := fun j hj =>
                hrest j (mem_of_mem_tail_dropWhile heqd hj)
              split at h
              · simp only [Option.map_eq_some_iff] at h
                obtain ⟨r, hr, rfl⟩ := h
                exact ⟨hpre,
                  fun j hj => hrest j (mem_of_mem_takeWhile' hj),
                  ih after r hafter hr⟩
              · exact absurd h (by simp)
          · exact absurd h (by simp)
      · -- forward conditional
        split at h
        · exact absurd h (by simp)
        · split at h
          · rename_i rest2 hsp2
            have hrest2 : ∀ m ∈ rest2, linstrRDirect m.li_i = true := fun m hm =>
              hrest m (mem_of_mem_tail2_dropWhile hsp2 hm)
            split at h
            · split at h
              · split at h
                · exact absurd h (by simp)
                · rename_i after heqd2
                  have hafter : ∀ x ∈ after, linstrRDirect x.li_i = true := fun x hx =>
                    hrest2 x (mem_of_mem_tail_dropWhile heqd2 hx)
                  split at h
                  · split at h
                    · simp only [Option.map_eq_some_iff] at h
                      obtain ⟨r, hr, rfl⟩ := h
                      exact ⟨hpre,
                        ⟨fun m hm => hrest2 m (mem_of_mem_takeWhile' hm),
                         fun m hm => hrest m (mem_of_mem_takeWhile' hm)⟩,
                        ih after r hafter hr⟩
                    · exact absurd h (by simp)
                  · exact absurd h (by simp)
              · exact absurd h (by simp)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
      · exact absurd h (by simp)

/-- **The addressing class crosses the recogniser.** When no operand of the
    emitted command is register-indexed, the structured control-flow block the
    recogniser returns has index-free straight-line leaves throughout — the
    hypothesis of `SpeculativeCTControlFlow.cfSpecExec_arch_mem_cfAddrs` and of
    the memory-address containment built on it. -/
theorem lcmdToOwnedCF_cfAllDirect {body : Lcmd} {cf : OwnedCF 64}
    (hd : lcmdDirect body = true) (h : lcmdToOwnedCF body = some cf) :
    CFAllDirect cf := by
  simp only [lcmdToOwnedCF, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk, hcf⟩ := h
  refine lcmdCFToOwnedCF_cfAllDirect k cf ?_ hcf
  refine parseLcmdCF_direct _ _ k ?_ hk
  intro i hi
  exact (lcmdDirect_iff body).mp hd i (List.mem_of_mem_filter hi)

/-- **A speculative memory event of a recognised branching body names a
    program-text address.** Composing the recogniser with
    `SpeculativeCTControlFlow.cfSpecExec_arch_mem_cfAddrs`: on an emitted command
    with no register-indexed operand, every memory access the speculative trace of
    the recognised block records — architectural or transient — is an access at a
    base register and compile-time displacement occurring in the block, for every
    predictor, window and state. -/
theorem lcmdToOwnedCF_spec_mem_cfAddrs {body : Lcmd} {cf : OwnedCF 64}
    (hd : lcmdDirect body = true) (h : lcmdToOwnedCF body = some cf)
    (window : Nat) (P : CFPredictor 64) (s : JState 64) (e : MachineConstantTime.MLeak)
    (he : SLeak.arch e ∈ (cfSpecExec window P s cf).1) : e ∈ cfAddrs cf :=
  SpeculativeCTControlFlow.cfSpecExec_arch_mem_cfAddrs window P cf
    (lcmdToOwnedCF_cfAllDirect hd h) s e he

/-! ## 5. The recogniser on an exported loop body

`JasminLprogExport.loopSmokePhysBody` is the physically-allocated body of the
front-lowered counted loop `loopSmokeProg` (`loopSmokePhysBody_expected` pins its
ten instructions): the accumulator seed, the counter seed `MOV RBX,#4`, the loop
label, one body copy, the counter decrement, the counter test and the back-edge
`Lcond NZ`. It is a body `GatherImmForms.gatherJBlock6` rejects, since it carries
a control transfer. -/

-- The skeleton of the exported loop body carries exactly one counted loop, whose
-- trip count is the `4` of `dblLoopBody`, read off the counter seed `MOV RBX,#4`.
#guard (parseLcmdCF ((loopSmokePhysBody ()).length + 1)
    ((loopSmokePhysBody ()).filter (fun i => !isLret i))).map LcmdCF.loopCounts = some [4]

-- The exported loop body recognises, leaves and all.
#guard (lcmdToOwnedCF (loopSmokePhysBody ())).isSome

-- No operand of the exported loop body is register-indexed, so
-- `lcmdToOwnedCF_cfAllDirect` applies to it.
#guard lcmdDirect (loopSmokePhysBody ())

-- A runtime trip count is outside the recogniser: `loopSmokeRtProg`'s lowered
-- body seeds its counter from an operand rather than a compile-time immediate.
#guard (lcmdToOwnedCF (loopSmokeRtBody ())).isNone

-- A register-indexed loop body is outside the recogniser's index-free
-- hypothesis: `mapAddOneProg` lowers its element access to `LOADIDX`/`STOREIDX`.
#guard !lcmdDirect (mapAddOneBodyV ())

end CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdToOwnedCF
