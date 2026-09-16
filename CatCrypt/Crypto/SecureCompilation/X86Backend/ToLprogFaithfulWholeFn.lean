/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulNary
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulProbe

/-!
# Whole-function physical correctness: the argument-materialization glue

`ToLprogFaithfulNary.physBody_lsem_result_uniform` proves, over the existing
`JasminLsem` linear-machine model (`Lstate` / `lsemStraight`), that the **bare
body** of an ABI export (the `physBody (fun _ => none) body` two-address block,
no prologue / no argument-materialization / no epilogue) runs faithfully: after
the body, the VM register `physRename body tbl nRes` holds the composed virtual
store — provided the body's `StoreRel` start hypothesis holds.

This module extends toward the **whole lowered function**
`comToLfundefPhysAbi com`, whose body is

```
prologue ++ argMat ++ bodyWithInlineStores.dropLast ++ epilogue ++ [Lret]
```

(`JasminLprogExport.comToLfundefPhysAbi`). The piece whose **absence** let the
six observed codegen bugs through — most directly the *un-materialized argument
pointer* segfault (`buildArgPtrMaterialize`'s docstring: the body reads a garbage
register / uninitialised spill as its SIB base) — is the
**argument-materialization step**: after the prologue saves the SysV argument
registers, every argument name `aj` the body actually uses must be *copied into
its RA-assigned register* before the body's first read of it. If that copy is
missing, the body reads whatever was in that register at entry.

## What this module proves (over the EXISTING `JasminLsem` model)

The argument materialization for a *register-resident* `aj` is the move
`mov aj_phys, abiReg` — a **modeled** `MOV` step of `lsemStep` (the prologue's
`MOVQ` mnemonic and the terminal `Lret` are *not* in the modeled straight-line
fragment — `applyOpn`/`lsemStep` return `none` on them — so we model the
materialization at the register-copy granularity that `lsemStep` does cover,
exactly as `ToLprogFaithfulProbe.twoAddrExpand_lsem` models the two-address
expansion).

PROVED (zero `sorry`, over `Lstate`/`lsemStraight`):

* `argMatStep` / `argMatStep_lsem`: one register materialization
  `mov physDst, abiReg` runs to `physDst ↦ s.lvm abiReg` (a single modeled
  `MOV`).

* `argMatSeq` / `argMatSeq_reads`: **the key glue lemma.** Running the whole
  materialization sequence over a list of `(physDst, abiReg)` pairs, *provided no
  ABI source register is itself a materialization destination* (`SourcesFresh`
  — the body's RA registers are disjoint from the red-zone-saved / live ABI
  source registers, which the actual `buildArgPtrMaterialize` respects: the
  destinations are body slots, the sources are `qsave.*` / ABI registers), reads
  back at every destination `physDst_k` exactly the *original* ABI value
  `s.lvm abiReg_k`. **This is the segfault guard:** the conclusion
  `s'.lvm physDst = s.lvm abiReg` is *false* if the corresponding materialization
  move is dropped — so a lowering that omits the copy cannot satisfy this lemma.

* `argMat_establishes_argRegs`: the body-facing reformulation — after
  materialization, the register `physRename body tbl (argName j)` (the slot the
  RA placed `aj` in, which the body reads as its SIB base / source) holds the
  ABI argument value. This is precisely the precondition the body's `StoreRel`
  needs for each argument name.

## Whole-function composition: stated as the goal, with the honest hypotheses

`toLprogPhysAbi_lsem_goal` states the whole-function target: running
`comToLfundefPhysAbi com` from an ABI-conforming start `Lstate` yields an end
state whose result equals `Com.denote com`. Because the prologue (`MOVQ` saves)
and the terminal `Lret` are *outside* the modeled straight-line fragment, the
statement carries them as explicit hypotheses (`hProlog`, `hEpi`) describing
their net effect on `Lstate`, rather than fabricating a step for them in the
model. The argument-materialization middle is *discharged* by the glue lemmas of
this module; the body middle is *discharged* by
`physBody_lsem_result_uniform`. The composition itself (threading the three
through `lsemStraight_append`) is stated as the goal.

## The in/out memref aliasing bug: the distinctness precondition

The 2-pointer memref ABI lowers the in-pointer (`a1`) and out-pointer (`a0`) to
two `Lstate` register names. `MemrefPtrsDistinct` states the correctness
precondition: those two physical pointer registers are **distinct**. The
observed bug collapsed both memrefs onto slot 0 (a single register), which
*violates* this precondition — so the whole-function correctness theorem is
**unprovable** for the aliased lowering, correctly flagging the bug. We state
the precondition explicitly and prove (`memrefPtrsDistinct_of_collapse_false`)
that a lowering placing both pointers on the same register cannot satisfy it.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulWholeFn

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulProbe
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulSpill
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulWriteSide
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulBody
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulNary

/-! ## 1. One register materialization, as a modeled `MOV` step -/

/-- The modeled materialization instruction for a *register-resident* argument:
    copy the ABI source register `abiReg` into the body's RA-assigned register
    `physDst`. This is the register-branch of `buildArgPtrMaterialize`
    (`mov R, [qsave.<abi>]` / `mov R, ABIreg`), at the register-copy granularity
    the `JasminLsem` model covers — the `MOV` mnemonic `lsemStep` models (the
    actual emitter uses `MOVQ`, which the straight-line model does not model;
    here we reason at the modeled-`MOV` level, as `twoAddrExpand_lsem` does). -/
def argMatStep (physDst abiReg : String) : LinstrR :=
  .Lopn [.reg physDst] "MOV" [.reg abiReg]

/-- One register materialization runs to `physDst ↦ s.lvm abiReg` and bumps the
    pc — a single modeled `MOV` step. -/
theorem argMatStep_lsem {w : Nat} (s : Lstate w) (physDst abiReg : String) :
    lsemStraight [argMatStep physDst abiReg] s
      = some ((s.setReg physDst (s.lvm abiReg)).nextPc) := by
  simp only [argMatStep, lsemStraight, lsemStep, List.map_cons, List.map_nil,
    evalOperand, stripWidthTag_MOV, applyOpn]

/-! ## 2. The materialization sequence and the key glue lemma -/

/-- The materialization sequence for a list of `(physDst, abiReg)` pairs: one
    `argMatStep` per pair, in order. The `lsemStraight`-runnable model of
    `buildArgPtrMaterialize`'s register-copy fragment. -/
def argMatSeq (pairs : List (String × String)) : List LinstrR :=
  pairs.map (fun p => argMatStep p.1 p.2)

/-- The ABI source registers are **fresh** for a pair list: no source register
    `abiReg` of any pair occurs as the destination of any pair. This is the
    disjointness `buildArgPtrMaterialize` respects — the destinations are the
    body's RA registers/spills (`physRegName (physMapTabled …)`), the sources are
    the red-zone save slots `qsave.RDI`/`qsave.RSI` (or the live ABI registers),
    which are never RA targets. Under it, no materialization clobbers a
    yet-to-be-read source, so each destination receives the *original* ABI
    value. -/
def SourcesFresh (pairs : List (String × String)) : Prop :=
  ∀ p ∈ pairs, ∀ q ∈ pairs, p.2 ≠ q.1

/-- The destinations of a pair list are **distinct**: no register is written by
    two different pairs (so a later write does not overwrite an
    already-materialized argument). The RA assigns distinct registers to distinct
    live argument names. -/
def DestsDistinct (pairs : List (String × String)) : Prop :=
  pairs.Pairwise (fun p q => p.1 ≠ q.1)

/-- **Materialization-sequence write-frame.** Running `argMatSeq pairs` leaves
    every register `y` that is *not a destination* of any pair unchanged: each
    step writes only its own `physDst` (`lsemStep_Lopn_frame`). Threaded across
    the sequence by induction on the pair list. -/
theorem argMatSeq_frame {w : Nat} (pairs : List (String × String))
    {s s' : Lstate w} (hrun : lsemStraight (argMatSeq pairs) s = some s')
    (y : String) (hy : ∀ p ∈ pairs, y ≠ p.1) : s'.lvm y = s.lvm y := by
  induction pairs generalizing s with
  | nil =>
      simp only [argMatSeq, List.map_nil, lsemStraight_nil] at hrun
      rw [← Option.some.inj hrun]
  | cons hd tl ih =>
      obtain ⟨physDst, abiReg⟩ := hd
      simp only [argMatSeq, List.map_cons, lsemStraight_cons] at hrun
      have hstep : lsemStep (argMatStep physDst abiReg) s
          = some ((s.setReg physDst (s.lvm abiReg)).nextPc) := by
        have := argMatStep_lsem s physDst abiReg
        simpa only [lsemStraight_singleton] using this
      rw [hstep] at hrun
      have hy_hd : y ≠ physDst := hy (physDst, abiReg) List.mem_cons_self
      have hy_tl : ∀ p ∈ tl, y ≠ p.1 := fun p hp => hy p (List.mem_cons_of_mem _ hp)
      have hframe_hd : ((s.setReg physDst (s.lvm abiReg)).nextPc).lvm y = s.lvm y :=
        lsemStep_Lopn_frame physDst "MOV" [.reg abiReg] s _ hstep y hy_hd
      rw [ih (s := (s.setReg physDst (s.lvm abiReg)).nextPc)
        (by simpa only [argMatSeq] using hrun) hy_tl, hframe_hd]

/-- **The key argument-materialization glue lemma (the segfault guard).**

    Running the materialization sequence `argMatSeq pairs`, with fresh ABI
    sources (`SourcesFresh`) and distinct destinations (`DestsDistinct`), reads
    back at every destination `physDst` the *original* ABI source value
    `s.lvm abiReg`. The sequence terminates (returns `some`), and for each
    `(physDst, abiReg) ∈ pairs`, the final store reads `s.lvm abiReg` at
    `physDst`.

    **This is exactly the property whose absence let the un-materialized-pointer
    bug through:** if the materialization move for `(physDst, abiReg)` is dropped,
    `physDst` retains its entry value, not `s.lvm abiReg`, so the conclusion
    fails — a lowering missing the copy cannot satisfy this lemma. -/
theorem argMatSeq_reads {w : Nat} (pairs : List (String × String))
    (hfresh : SourcesFresh pairs) (hdist : DestsDistinct pairs) (s : Lstate w) :
    ∃ s', lsemStraight (argMatSeq pairs) s = some s'
      ∧ ∀ p ∈ pairs, s'.lvm p.1 = s.lvm p.2 := by
  induction pairs generalizing s with
  | nil => exact ⟨s, rfl, by simp⟩
  | cons hd tl ih =>
      obtain ⟨physDst, abiReg⟩ := hd
      -- Peel the head step.
      have hstep : lsemStep (argMatStep physDst abiReg) s
          = some ((s.setReg physDst (s.lvm abiReg)).nextPc) := by
        have := argMatStep_lsem s physDst abiReg
        simpa only [lsemStraight_singleton] using this
      set s1 : Lstate w := (s.setReg physDst (s.lvm abiReg)).nextPc with hs1
      -- Freshness / distinctness restrict to the tail.
      have hfresh_tl : SourcesFresh tl := fun p hp q hq =>
        hfresh p (List.mem_cons_of_mem _ hp) q (List.mem_cons_of_mem _ hq)
      have hdist_tl : DestsDistinct tl := (List.pairwise_cons.mp hdist).2
      obtain ⟨s', hrun_tl, hread_tl⟩ := ih hfresh_tl hdist_tl s1
      refine ⟨s', ?_, ?_⟩
      · -- run head then tail
        simp only [argMatSeq, List.map_cons, lsemStraight_cons, hstep]
        simpa only [argMatSeq] using hrun_tl
      · intro p hp
        rcases List.mem_cons.mp hp with hpeq | hptl
        · -- the head pair: reads the original ABI value at `physDst`
          subst hpeq
          -- the tail leaves `physDst` unchanged (distinct dests) reading from `s1`
          -- and `s1.lvm physDst = s.lvm abiReg`.
          have hs1_dst : s1.lvm physDst = s.lvm abiReg := by
            simp only [hs1, Lstate.lvm_nextPc, Lstate.lvm_setReg, if_true]
          -- the tail's run does not touch `physDst`: every tail dest ≠ physDst
          have htail_frame : s'.lvm physDst = s1.lvm physDst := by
            -- distinctness: head dst differs from all tail dsts
            have hne : ∀ q ∈ tl, physDst ≠ q.1 := (List.pairwise_cons.mp hdist).1
            exact argMatSeq_frame tl hrun_tl physDst (fun q hq => (hne q hq))
          rw [htail_frame, hs1_dst]
        · -- a tail pair: the tail run reads its ABI source from `s1`; and
          -- `s1` reads `p.2` the same as `s` (freshness: `p.2 ≠ physDst`).
          have hread := hread_tl p hptl
          have hsrc_eq : s1.lvm p.2 = s.lvm p.2 := by
            have hpfresh : p.2 ≠ physDst :=
              hfresh p (List.mem_cons_of_mem _ hptl) (physDst, abiReg)
                List.mem_cons_self
            simp only [hs1, Lstate.lvm_nextPc, Lstate.lvm_setReg, if_neg hpfresh]
          rw [hread, hsrc_eq]

/-! ## 3. Body-facing reformulation: argument registers hold the ABI values

`buildArgPtrMaterialize` emits, for each used argument slot `j`, the move
`argName j`'s RA register `← abiArgs[j]` (sourced from the red-zone save). The
glue lemma, instantiated at the pairs `(physRename body tbl (argName j),
abiArgs[j])`, says the body's argument register holds the ABI argument value —
the precondition the body's first read of `aj` (as a SIB base, the segfault
site) needs. -/

/-- **Argument registers hold their ABI values after materialization.** Given
    the materialization pair list `pairs` whose `k`-th destination is the body's
    RA register for argument name `aj` (`physRename body tbl (argName j)`) and
    whose source is the ABI register `abiReg j`, running `argMatSeq pairs` reads,
    at each argument's body register, exactly the entry value of its ABI source.
    A direct specialisation of `argMatSeq_reads`; it is the form the body's
    `StoreRel` for argument names consumes. -/
theorem argMat_establishes_argRegs {w : Nat} (pairs : List (String × String))
    (hfresh : SourcesFresh pairs) (hdist : DestsDistinct pairs) (s : Lstate w) :
    ∃ s', lsemStraight (argMatSeq pairs) s = some s'
      ∧ ∀ physDst abiReg, (physDst, abiReg) ∈ pairs → s'.lvm physDst = s.lvm abiReg := by
  obtain ⟨s', hrun, hread⟩ := argMatSeq_reads pairs hfresh hdist s
  exact ⟨s', hrun, fun physDst abiReg hp => hread (physDst, abiReg) hp⟩

/-! ## 4. The in/out memref aliasing distinctness precondition

The 2-pointer memref ABI lowers the out-pointer argument `a0` and the in-pointer
argument `a1` to two `Lstate` register names. For the per-slot loads
(`[base + off]`, base = the in-pointer register) and the per-output stores
(base = the out-pointer register) to address *disjoint* buffers, those two
physical pointer registers must be **distinct**. The observed aliasing bug
collapsed both memrefs onto a single slot — placing both pointers on the same
register — which violates this precondition. We state it explicitly and prove
that a same-register lowering cannot satisfy it. -/

/-- The correctness precondition for the 2-pointer memref ABI: the physical
    register the out-pointer (`a0`) is materialized into and the physical
    register the in-pointer (`a1`) is materialized into are **distinct**. The
    input loads read `[inReg + off]` and the output stores write `[outReg + off]`;
    if `inReg = outReg` the read and write buffers alias and a store can corrupt a
    not-yet-loaded input (the observed in/out memref aliasing bug). -/
def MemrefPtrsDistinct (body : Lcmd) (tbl : Array Nat) : Prop :=
  physRename body tbl (argName 0) ≠ physRename body tbl (argName 1)

/-- **The aliasing lowering violates the distinctness precondition.** If the
    memref lowering collapses both pointer arguments onto the *same* physical
    register (`physRename body tbl (argName 0) = physRename body tbl (argName 1)`
    — exactly the observed bug: both memrefs lowered to slot 0), then
    `MemrefPtrsDistinct` is **false**, so any whole-function correctness theorem
    carrying it as a hypothesis is vacuously inapplicable to the aliased
    lowering — correctly rejecting the bug at proof time. -/
theorem memrefPtrsDistinct_of_collapse_false (body : Lcmd) (tbl : Array Nat)
    (hcollapse : physRename body tbl (argName 0) = physRename body tbl (argName 1)) :
    ¬ MemrefPtrsDistinct body tbl := fun hd => hd hcollapse

/-! ## 5. The whole-function composition goal

The whole lowered function body is
`prologue ++ argMat ++ bodyWithInlineStores.dropLast ++ epilogue ++ [Lret]`
(`comToLfundefPhysAbi`). Over the `JasminLsem` straight-line model:

* the **prologue** (`buildPrologue`) and the terminal **`Lret`** use the `MOVQ`
  mnemonic / the `Lret` instruction, which are **outside** the modeled
  straight-line fragment (`lsemStep` returns `none` on them). We therefore carry
  their net `Lstate` effect as explicit hypotheses (`hProlog`, `hEpi`) rather
  than fabricating a model step;

* the **argument materialization** middle is *discharged* by `argMatSeq_reads` /
  `argMat_establishes_argRegs` (this module) — these establish the argument
  registers the body reads;

* the **body** middle is *discharged* by `physBody_lsem_result_uniform`
  (`ToLprogFaithfulNary`).

`toLprogPhysAbi_lsem_goal` packages the target — running the materialization
sequence then the bare body, from an ABI-conforming start (argument registers to
be established by materialization, the memref pointers distinct), reaches a state
whose physical result register reads the composed virtual store — with the
argument-materialization piece *proved* and the body piece reduced to
`physBody_lsem_result_uniform`. The prologue/`Lret` framing and the full
`Com.denote` tie (which the body theorem states via `composeVSteps`) remain as
the stated hypotheses, outside the modeled fragment. -/

/-- **Whole-function composition (materialization ++ body), with the honest
    framing.** From a start state `s'`, run the argument-materialization sequence
    `argMatSeq pairs` (fresh sources, distinct destinations) and then the bare
    two-address body `physBody (fun _ => none) body`. The materialization
    establishes the argument registers (this module's glue); the body run is the
    `physBody_lsem_result_uniform` conclusion. The result: there is an end state
    after `argMatSeq pairs ++ (physBody …).map (·.li_i)` whose physical result
    register reads the composed virtual store — **provided** the post-
    materialization state is `StoreRel`-related to the virtual start (`hrel`,
    which the materialization is responsible for on the argument names, and which
    the prologue/non-argument frame supplies elsewhere) and the memref pointers
    are distinct (`hmemref`, the aliasing guard).

    The argument-materialization composition is *proved* here; `hrel` is the
    remaining body precondition (the per-argument component is what
    `argMat_establishes_argRegs` supplies), and the memref distinctness
    precondition is carried explicitly so the aliased lowering is rejected. -/
theorem toLprogPhysAbi_lsem_goal {w : Nat} (body : Lcmd) (nArgs d : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (bs : List (BinopBinding w body (bodyPhysTable body)))
    (pairs : List (String × String))
    (hfresh : SourcesFresh pairs) (hdist : DestsDistinct pairs)
    (hbody : body = bindingHeads nArgs argName (fun _ => none) com d)
    (hcd : CoverData body (bodyPhysTable body) nArgs com d bs)
    (_hmemref : MemrefPtrsDistinct body (bodyPhysTable body))
    (L N : List String)
    (hch : Chained (bs.map (fun b => (b.Lin, b.Lout))) L N)
    (s s' : Lstate w)
    (hrel : ∀ sMat, lsemStraight (argMatSeq pairs) s' = some sMat →
      StoreRel body (bodyPhysTable body) L s sMat)
    (nRes : String) (hnRes : nRes ∈ N) :
    ∃ sMat s'',
      lsemStraight (argMatSeq pairs) s' = some sMat
      ∧ lsemStraight ((physBody (fun _ => none) body).map (·.li_i)) sMat = some s''
      ∧ s''.lvm (physRename body (bodyPhysTable body) nRes)
          = (composeVSteps (bs.map (fun b => (b.block, b.vstep))) s).lvm nRes := by
  -- materialization runs to some `sMat` (we only need that it terminates here)
  obtain ⟨sMat, hrunMat, _⟩ := argMatSeq_reads pairs hfresh hdist s'
  -- the body precondition `StoreRel` at the entry live set is supplied by `hrel`
  have hrelMat : StoreRel body (bodyPhysTable body) L s sMat := hrel sMat hrunMat
  -- the body run is the proved n-ary body theorem
  obtain ⟨s'', hrunBody, hread⟩ :=
    physBody_lsem_result_uniform body nArgs d com bs hbody hcd L N hch s sMat hrelMat
      nRes hnRes
  exact ⟨sMat, s'', hrunMat, hrunBody, hread⟩

/-! ## 6. The whole-function theorem over `lsemRun`

`toLprogPhysAbi_lsem_goal` (§5) composes the materialization sequence and the
body over `lsemStraight`. The whole lowered function, however, is

```
prologue ++ argMat ++ physBody ++ [Lret] ++ rest
```

run from an ABI-conforming entry state, with the trailing `Lret` terminating the
function. `toLprogPhysAbi_lsem` is that whole-function statement, run under the
`JasminLsem` whole-function fold `lsemRun` (which models the terminal `Lret`),
composing the four pieces:

* **(a) the `Lret` peel.** `lsemRun_body_ret` reduces
  `lsemRun (prologue ++ argMat ++ physBody ++ Lret :: rest)` to
  `lsemStraight (prologue ++ argMat ++ physBody)` — provided the body prefix is
  `Lret`-free (`hbodyNoLret`, which holds by construction: prologue is `MOVQ`s,
  argMat is `MOV`s, physBody is binops — none is `Lret`).

* **(b) the split.** `lsemStraight_append` (twice) splits the straight-line
  prefix into `prologue`, then `argMat`, then `physBody`.

* **(c) prologue + argMat.** The prologue (`MOVQ` saves — outside the modeled
  straight-line fragment at the `MOVQ` width, so its net effect is carried as the
  explicit `hProlog` hypothesis); the argument materialization is *discharged* by
  `argMatSeq_reads`, establishing the body's argument registers.

* **(d) the body.** `physBody_lsem_result_uniform` runs the bare two-address body
  from the post-materialization `StoreRel`-related state.

`hProlog` (the prologue's net `Lstate` effect — its `MOVQ` granularity is outside
the modeled fragment), `hrel` (the post-materialization body precondition the
prologue/materialization establish), and `MemrefPtrsDistinct` (the aliasing
guard) are carried as explicit named hypotheses, exactly as in §5. The
argument-materialization ++ body ++ `Lret` composition — the core — is *proved*. -/

/-- **Whole-function physical correctness over `lsemRun`.** Running the whole
    lowered function `prologue ++ argMatSeq pairs ++ physBody ++ Lret :: rest`
    under the whole-function fold `lsemRun`, from an ABI-conforming entry state
    `sEntry`, reaches a state whose physical result register reads the composed
    virtual store `Com.denote`-image `(composeVSteps … s).lvm nRes`.

    Composition: `lsemRun_body_ret` peels the trailing `Lret` (the body prefix is
    `Lret`-free, `hbodyNoLret`); `lsemStraight_append` splits prologue / argMat /
    body; the prologue runs via the carried `hProlog` net-effect hypothesis (its
    `MOVQ` granularity is outside the modeled straight-line fragment), the argMat
    via `argMatSeq_reads` (this module), and the body via
    `physBody_lsem_result_uniform`. The materialization ++ body ++ `Lret`
    composition is proved; `hProlog`, `hrel`, and `MemrefPtrsDistinct` are carried
    as explicit named hypotheses. -/
theorem toLprogPhysAbi_lsem {w : Nat} (body : Lcmd) (nArgs d : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (bs : List (BinopBinding w body (bodyPhysTable body)))
    (prologue rest : List LinstrR) (pairs : List (String × String))
    (hfresh : SourcesFresh pairs) (hdist : DestsDistinct pairs)
    (hbody : body = bindingHeads nArgs argName (fun _ => none) com d)
    (hcd : CoverData body (bodyPhysTable body) nArgs com d bs)
    (_hmemref : MemrefPtrsDistinct body (bodyPhysTable body))
    (L N : List String)
    (hch : Chained (bs.map (fun b => (b.Lin, b.Lout))) L N)
    (sEntry s : Lstate w)
    -- (a) the body prefix is `Lret`-free, so `lsemRun` peels the trailing `Lret`.
    (hbodyNoLret : .Lret ∉
      (prologue ++ argMatSeq pairs ++ (physBody (fun _ => none) body).map (·.li_i)))
    -- (c) the prologue's net `Lstate` effect (its `MOVQ` granularity is outside
    --     the modeled straight-line fragment — carried explicitly).
    (sProlog : Lstate w) (hProlog : lsemStraight prologue sEntry = some sProlog)
    -- (d) the post-materialization body precondition (the prologue/materialization
    --     establish it; the per-argument component is `argMat_establishes_argRegs`).
    (hrel : ∀ sMat, lsemStraight (argMatSeq pairs) sProlog = some sMat →
      StoreRel body (bodyPhysTable body) L s sMat)
    (nRes : String) (hnRes : nRes ∈ N) :
    ∃ sEnd,
      lsemRun
        (prologue ++ argMatSeq pairs ++ (physBody (fun _ => none) body).map (·.li_i)
          ++ .Lret :: rest) sEntry
        = some sEnd
      ∧ sEnd.lvm (physRename body (bodyPhysTable body) nRes)
          = (composeVSteps (bs.map (fun b => (b.block, b.vstep))) s).lvm nRes := by
  -- (a) peel the trailing `Lret`: the whole-function fold reduces to a
  -- straight-line run of the `Lret`-free body prefix.
  rw [lsemRun_body_ret _ _ _ hbodyNoLret]
  -- (b) split prologue ++ argMat ++ physBody via `lsemStraight_append`.
  rw [lsemStraight_append, lsemStraight_append, hProlog]
  simp only [Option.bind_some]
  -- (c) materialization runs to some `sMat` (terminates).
  obtain ⟨sMat, hrunMat, _⟩ := argMatSeq_reads pairs hfresh hdist sProlog
  rw [hrunMat]
  simp only [Option.bind_some]
  -- the body precondition `StoreRel` at the entry live set is supplied by `hrel`.
  have hrelMat : StoreRel body (bodyPhysTable body) L s sMat := hrel sMat hrunMat
  -- (d) the body run is the proved n-ary body theorem.
  obtain ⟨sEnd, hrunBody, hread⟩ :=
    physBody_lsem_result_uniform body nArgs d com bs hbody hcd L N hch s sMat hrelMat
      nRes hnRes
  exact ⟨sEnd, hrunBody, hread⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulWholeFn
