/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.WellFormedX86
public import CatCrypt.Crypto.SecureCompilation.X86Backend.WellFormedX86
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulWholeFn
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulWholeFn

/-!
# `ValidateLowering`: a decidable translation-validation gate for the owned lowering

`ToLprogFaithfulWholeFn.toLprogPhysAbi_lsem` is the proved whole-function spec for
the owned x86 lowering: running the lowered function `prologue ++ argMatSeq ++
physBody ++ Lret :: rest` under `lsemRun` reaches a state whose physical result
register reads the composed virtual store (the `Com.denote`-image). But it carries
*explicit physical-realization preconditions* whose absence let the six observed
codegen bugs through:

* `MemrefPtrsDistinct body tbl` — the two pointer arguments resolve to **distinct**
  physical registers (the in/out memref aliasing guard; `as`/`gdb` could not catch
  it — a collapsed-onto-one-register lowering segfaults at run time);
* the argument-materialization premise — every argument register the body reads as a
  SIB base is written (materialized) in the prologue **before** its first use
  (`argMatSeq_reads`'s `SourcesFresh`/`DestsDistinct` and the body-facing
  `argMat_establishes_argRegs`; an un-materialized base reads a garbage register →
  segfault);
* operand legality — `wfLprog` (`WellFormedX86`): at most one memory operand per
  `Lopn` (the `mem → mem` movs) and every operand resolved (no `%<UNKNOWN:k.N>`
  unresolved-spill sentinel `as` rejects).

This module turns those preconditions into a **single decidable `Bool` predicate**
`validateLowering : Lprog → (String → Lcmd × Array Nat) → Nat → Nat → Bool` (the
`Lprog`, plus the per-function virtual-body+table the lowering produced, the
pointer-arg count, and the spill stride) that the orchestrator runs *at lowering
time*, gating wide kernels before any text reaches `as`/`gdb`.
`validateLowering p virtFor nPtr framePerSlot = true` discharges (the decidable
forms of) the preconditions `toLprogPhysAbi_lsem` needs.

## The four clauses (each a decidable `Bool` predicate over the instruction list)

* **(a) operand legality** — `WellFormedX86.wfLprog p`. Reused wholesale: at most
  one memory operand per `Lopn` (bug classes 1, 2) and every operand resolved
  (bug class 3). Soundness via `WellFormedX86.wfLinstr_sound`.

* **(b) memref/pointer distinctness** — the function's declared distinct pointer
  arguments resolve to **distinct** physical registers. Decidable form of
  `MemrefPtrsDistinct`. Built with the **`JointScheduleRegAlloc.renameInjective`
  aliasing-check idea**: `Nodup` over the mapped image of the pointer-argument
  names under the physical renaming `physRename body tbl`. For two pointers this
  is exactly `physRename … (argName 0) ≠ physRename … (argName 1)`.

* **(c) argument materialization** — every argument register the body uses as a
  SIB **base** is written by some earlier instruction (the prologue/materialization
  `mov`) before its first read. Decidable form of `argMatSeq_reads`'s premise: the
  `firstWriteIdx` of each used argument base precedes its `firstReadIdx`.

* **(d) spill consistency** — every spill-slot reference `k.<n>` resolves to a
  concrete in-frame offset (no `%<UNKNOWN>` placeholder — already implied by
  `wfLprog`'s `opResolved`, restated here as the spill-specific obligation) **and**
  the function's frame size covers the maximum spill slot index used.

## Soundness (`validateLowering_sound` + the explicit bridge goals)

`validateLowering_sound` proves that `validateLowering p = true` entails the clauses
that follow directly from the decidable checks plus `wfLinstr_sound`:

* the `wfLprog` clause (operand legality) — fully proved;
* the no-unresolved-spill clause — fully proved (a corollary of `opResolved`);
* the **memref-distinctness clause**, in the decidable `Nodup`/`≠` form — fully
  proved, and bridged to the *semantic* `MemrefPtrsDistinct` for the two-pointer
  case (`validate_memrefDistinct_two`, via `memrefPtrsDistinct_of_collapse_false`
  reasoning: a same-register lowering fails the `≠` check).

For the **argument-materialization** clause, whose semantic form is the
`StoreRel`/`SourcesFresh`/`DestsDistinct` premise of `argMatSeq_reads` (a statement
about the *prologue's net `Lstate` effect*, which is outside the modeled
straight-line fragment — see `toLprogPhysAbi_lsem`'s `hProlog`), the decidable→
semantic bridge cannot be closed inside this module without the prologue model.
We therefore state it as an **explicit named goal**
(`validate_argMat_bridge_goal`) and prove the decidable direction we can — the
`firstWriteIdx`/`firstReadIdx` ordering is decidable and discharged by the checker.

The KEY deliverable: `validateLowering p = true` discharges
`MemrefPtrsDistinct` (clause b), the no-unresolved-spill obligation (clause d), and
`wfLprog` (clause a) — the three preconditions whose decidable→semantic bridge is
fully closable here.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ValidateLowering

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.WellFormedX86
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulWholeFn
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulSpill

/-! ## 0. Operand-name extraction helpers (decidable, over the instruction list) -/

/-- The destination register names written by one `LinstrR` (the `.reg` dsts of an
    `Lopn`; control-flow leaves write nothing for materialization purposes). The
    materialization/prologue `mov`s write their destination register — this is what
    clause (c) tracks as "the arg base was materialized". -/
def writtenRegs : LinstrR → List String
  | .Lopn dsts _ _ => dsts.filterMap LOperand.regName?
  | _ => []

/-- The SIB **base** register names read by one `LinstrR`. A `.arrIdx base idx _`
    source addresses memory through `base`; clause (c) requires `base` to have been
    materialized before this read (else the body reads a garbage register as its
    address — the un-materialized-pointer segfault). -/
def sibBaseReads : LinstrR → List String
  | .Lopn _ _ srcs =>
      srcs.filterMap (fun o => match o with
        | .arrIdx base _ _ => some base
        | _ => none)
  | _ => []

/-- All spill-slot **names** (`k.<n>`) referenced by one `LinstrR` across its
    operands — the names clause (d) checks resolve to a concrete in-frame offset. -/
def spillNamesOf (i : LinstrR) : List String :=
  (instrOperands i).filterMap (fun o => match o with
    | .reg n => if "k.".isPrefixOf n then some n else none
    | _ => none)

/-- Parse a resolved spill name `k.<n>` to its slot index `<n>`; `none` for a name
    that is not a parseable `k.<n>`. -/
def spillSlotIndex (n : String) : Option Nat :=
  if "k.".isPrefixOf n then String.toNat? (n.drop 2).toString else none

/-! ## 1. Clause (b): memref/pointer distinctness (the `renameInjective` idea)

The `JointScheduleRegAlloc.renameInjective` pattern: a renaming is non-aliasing on
a name set iff `Nodup` holds over the mapped image. Here the "renaming" is the
physical lowering `physRename body tbl`, and the name set is the function's
*distinct pointer arguments* (`argName 0, argName 1, …`). `Nodup` over their images
says the pointers occupy distinct physical registers — the decidable form of
`MemrefPtrsDistinct`. -/

/-- The pointer-argument names of an `nPtr`-pointer memref ABI: `argName 0 …
    argName (nPtr-1)`. -/
def ptrArgNames (nPtr : Nat) : List String :=
  (List.range nPtr).map argName

/-- **Clause (b), decidable.** The `nPtr` pointer arguments resolve to **distinct**
    physical registers: `Nodup` over the image of `ptrArgNames` under
    `physRename body tbl` — the `renameInjective` aliasing check, instantiated at
    the lowering renaming. The aliasing bug (both pointers on one register) makes
    the image have a duplicate, so `Nodup` fails. -/
def memrefPtrsDistinctB (body : Lcmd) (tbl : Array Nat) (nPtr : Nat) : Bool :=
  ((ptrArgNames nPtr).map (physRename body tbl)).Nodup

/-! ## 2. Clause (c): argument materialization (write-before-first-use)

`argMatSeq_reads` requires the materialization sequence to write each argument's
body register before the body reads it as a SIB base. The decidable witness: in the
flat instruction list, the *first write* of an argument base register precedes its
*first read* as a SIB base. An un-materialized base has no earlier write, so the
check fails. -/

/-- The index of the first instruction in `is` that writes register `r` (as an
    `Lopn` destination), or `none` if `r` is never written. -/
def firstWriteIdx (is : List LinstrR) (r : String) : Option Nat :=
  (is.findIdx? (fun i => (writtenRegs i).contains r))

/-- The index of the first instruction in `is` that reads register `r` as a SIB
    base, or `none` if `r` is never so read. -/
def firstSibReadIdx (is : List LinstrR) (r : String) : Option Nat :=
  (is.findIdx? (fun i => (sibBaseReads i).contains r))

/-- An argument base register is **materialized before use** iff, whenever it is
    read as a SIB base at index `ri`, it is written at some index `wi < ri`. -/
def materializedBeforeUse (is : List LinstrR) (r : String) : Bool :=
  match firstSibReadIdx is r with
  | none => true                         -- never used as a base ⇒ nothing to guard
  | some ri =>
      match firstWriteIdx is r with
      | none => false                    -- read-as-base but never written ⇒ segfault
      | some wi => decide (wi < ri)

/-- All SIB-base register names read anywhere in the instruction list. -/
def allSibBases (is : List LinstrR) : List String :=
  (is.flatMap sibBaseReads).eraseDups

/-- **Clause (c), decidable.** Every SIB base the body reads is materialized before
    its first use — the decidable form of `argMatSeq_reads`'s premise (the
    materialization writes the body's argument registers before the body reads
    them). -/
def argsMaterialized (is : List LinstrR) : Bool :=
  (allSibBases is).all (fun r => materializedBeforeUse is r)

/-! ## 3. Clause (d): spill consistency (resolved + in-frame) -/

/-- All spill names referenced anywhere in the instruction list. -/
def allSpillNames (is : List LinstrR) : List String :=
  (is.flatMap spillNamesOf).eraseDups

/-- Every spill name in the list parses to a concrete slot index (no `%<UNKNOWN>`
    placeholder). A corollary of `wfLprog`'s `opResolved`, restated as the
    spill-specific obligation clause (d) carries. -/
def spillsResolved (is : List LinstrR) : Bool :=
  (allSpillNames is).all (fun n => (spillSlotIndex n).isSome)

/-- The maximum spill slot index used in the list (`0` if no spills). -/
def maxSpillSlot (is : List LinstrR) : Nat :=
  (allSpillNames is).foldl
    (fun acc n => max acc ((spillSlotIndex n).getD 0)) 0

/-- **Clause (d), decidable.** Every spill reference resolves to a concrete slot
    index, and the frame size (`framePerSlot * (maxSpillSlot + 1)`) does not exceed
    the declared `frameSize`. The `framePerSlot` byte stride is the spill-slot width
    (8 bytes for a GP spill); a `maxSpillSlot` past the frame is the unresolved /
    out-of-frame spill `as` cannot place. -/
def spillConsistentB (is : List LinstrR) (frameSize framePerSlot : Nat) : Bool :=
  spillsResolved is &&
    decide (framePerSlot * (maxSpillSlot is + 1) ≤ frameSize)

/-! ## 4. The decidable validator -/

/-- The instruction list of a function body. -/
def bodyInstrs (fd : Lfundef) : List LinstrR :=
  fd.lfd_body.map Linstr.li_i

/-- **The decidable per-function lowering validator.** A lowering is a pair of a
    **virtual body** `virtBody` (the pre-RA two-address body, over which clause (b)'s
    `MemrefPtrsDistinct` is phrased — it computes `physRename virtBody tbl`) with its
    rename table `tbl`, and the resulting **physical** function `fd` (the lowered,
    physical-register body, over which clauses (a)/(c)/(d) are phrased). Given the
    pointer-argument count `nPtr` and the per-slot frame stride `framePerSlot`, a
    lowering passes iff all four clauses hold:

    (a) `wfLfundef fd` — operand legality (≤ 1 memory operand, every operand
        resolved) of the **physical** body;
    (b) `memrefPtrsDistinctB virtBody tbl nPtr` — the pointer args resolve to
        distinct physical registers (decidable `MemrefPtrsDistinct virtBody tbl`);
    (c) `argsMaterialized` — every SIB base in the **physical** body is written
        before its first use;
    (d) `spillConsistentB` — every spill in the **physical** body resolves and the
        frame covers the max slot.

    This is the decidable conjunction of the preconditions `toLprogPhysAbi_lsem`
    needs. (Clause (b) is over the *virtual* body+table because that is exactly
    `MemrefPtrsDistinct`'s definitional shape; the other clauses are over the
    physical lowered body the gate inspects.) -/
def validateLfundefWith (virtBody : Lcmd) (tbl : Array Nat) (fd : Lfundef)
    (nPtr framePerSlot : Nat) : Bool :=
  wfLfundef fd &&
  memrefPtrsDistinctB virtBody tbl nPtr &&
  argsMaterialized (bodyInstrs fd) &&
  spillConsistentB (bodyInstrs fd) fd.lfd_frame_size framePerSlot

/-- **The decidable whole-program lowering validator.** Runs `validateLfundefWith`
    on every function. The lowering supplies, per function name, its **virtual**
    body + rename table (the clause-(b) input — the same `(body, tbl)` pair
    `comToLfundefPhysAbi` lowers and over which `MemrefPtrsDistinct` is phrased);
    the physical lowered function is taken from `p`. `nPtr` (pointer-arg count) and
    `framePerSlot` (spill stride, 8 for GP) are lowering parameters. The
    post-lowering gate the orchestrator runs. The `virtFor` lookup defaults to the
    physical body when the lowering ships no separate virtual record (a 1:1
    physical lowering, where clause (b) then checks the physical body directly). -/
def validateLowering (p : Lprog) (virtFor : String → Lcmd × Array Nat)
    (nPtr framePerSlot : Nat) : Bool :=
  p.lp_funcs.all (fun e =>
    validateLfundefWith (virtFor e.1).1 (virtFor e.1).2 e.2 nPtr framePerSlot)

/-- The validator is runnable (decidable as `= true`). -/
example (p : Lprog) (virtFor : String → Lcmd × Array Nat) (nPtr framePerSlot : Nat) :
    Decidable (validateLowering p virtFor nPtr framePerSlot = true) := inferInstance

/-! ## 5. Soundness: `validate = true` discharges the preconditions

We prove the clauses whose decidable→semantic bridge is closable inside this
module: the `wfLprog` clause (a, via `wfLinstr_sound`), the no-unresolved-spill
clause (d), and the memref-distinctness clause (b) in both its decidable `Nodup`
form and — for the two-pointer ABI — its semantic `MemrefPtrsDistinct` form. The
argument-materialization clause's semantic form is stated as an explicit named
goal. -/

/-! ### 5a. Per-function projection of each clause from the conjunction -/

/-- `validateLfundefWith = true` projects to clause (a): the body is `wfLfundef`. -/
theorem validate_wf {virtBody : Lcmd} {fd : Lfundef} {tbl : Array Nat}
    {nPtr framePerSlot : Nat}
    (h : validateLfundefWith virtBody tbl fd nPtr framePerSlot = true) :
    wfLfundef fd = true := by
  unfold validateLfundefWith at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  exact h.1.1.1

/-- `validateLfundefWith = true` projects to clause (b): `memrefPtrsDistinctB`. -/
theorem validate_memrefDistinctB {virtBody : Lcmd} {fd : Lfundef} {tbl : Array Nat}
    {nPtr framePerSlot : Nat}
    (h : validateLfundefWith virtBody tbl fd nPtr framePerSlot = true) :
    memrefPtrsDistinctB virtBody tbl nPtr = true := by
  unfold validateLfundefWith at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  exact h.1.1.2

/-- `validateLfundefWith = true` projects to clause (c): `argsMaterialized`. -/
theorem validate_argsMaterialized {virtBody : Lcmd} {fd : Lfundef} {tbl : Array Nat}
    {nPtr framePerSlot : Nat}
    (h : validateLfundefWith virtBody tbl fd nPtr framePerSlot = true) :
    argsMaterialized (bodyInstrs fd) = true := by
  unfold validateLfundefWith at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  exact h.1.2

/-- `validateLfundefWith = true` projects to clause (d): `spillConsistentB`. -/
theorem validate_spillConsistent {virtBody : Lcmd} {fd : Lfundef} {tbl : Array Nat}
    {nPtr framePerSlot : Nat}
    (h : validateLfundefWith virtBody tbl fd nPtr framePerSlot = true) :
    spillConsistentB (bodyInstrs fd) fd.lfd_frame_size framePerSlot = true := by
  unfold validateLfundefWith at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  exact h.2

/-! ### 5b. Clause (a) → semantic: every body instruction satisfies `wfLinstr_sound` -/

/-- **Clause (a) soundness (bridged).** If a function passes the validator, every
    instruction of its body satisfies the two assemble-legality properties `as`
    needs (`atMostOneMemOperand ∧ allOperandsResolved`) — the direct corollary of
    `wfLfundef` + `WellFormedX86.wfLinstr_sound`. This discharges bug classes 1, 2,
    3 at lowering time. -/
theorem validate_wfLinstr_sound {virtBody : Lcmd} {fd : Lfundef} {tbl : Array Nat}
    {nPtr framePerSlot : Nat}
    (h : validateLfundefWith virtBody tbl fd nPtr framePerSlot = true) :
    ∀ i ∈ fd.lfd_body, atMostOneMemOperand i.li_i ∧ allOperandsResolved i.li_i := by
  have hwf : wfLfundef fd = true := validate_wf h
  unfold wfLfundef wfLcmd at hwf
  intro i hi
  have := (List.all_eq_true.mp hwf) i hi
  exact wfLinstr_sound i.li_i this

/-! ### 5c. Clause (b) → semantic: the memref-distinctness discharge

The decidable `Nodup` clause discharges the semantic `MemrefPtrsDistinct` for the
two-pointer memref ABI. This is the KEY discharge: `validate = true ⇒
MemrefPtrsDistinct`, the aliasing guard that `as`/`gdb` could not provide.
`memrefPtrsDistinct_of_collapse_false` is the contrapositive witness — a
same-register lowering fails the `Nodup` check below. -/

/-- For the two-pointer ABI, the decidable `Nodup` clause is exactly
    `physRename … (argName 0) ≠ physRename … (argName 1)`. -/
theorem memrefPtrsDistinctB_two_iff (body : Lcmd) (tbl : Array Nat) :
    memrefPtrsDistinctB body tbl 2 = true ↔
      physRename body tbl (argName 0) ≠ physRename body tbl (argName 1) := by
  have hlist : (ptrArgNames 2).map (physRename body tbl)
      = [physRename body tbl (argName 0), physRename body tbl (argName 1)] := by
    rfl
  unfold memrefPtrsDistinctB
  rw [hlist]
  -- `decide ([a, b].Nodup) = true ↔ a ≠ b`
  simp only [decide_eq_true_eq, List.nodup_cons, List.mem_singleton,
    List.not_mem_nil, List.nodup_nil, and_true, List.mem_cons, or_false, ne_eq,
    not_false_eq_true]

/-- **Clause (b) soundness (the KEY discharge — bridged to the semantic form).** If
    a two-pointer-ABI function passes the validator, the semantic precondition
    `MemrefPtrsDistinct fd.lfd_body tbl` of `toLprogPhysAbi_lsem` **holds**: the two
    pointer arguments resolve to distinct physical registers. This is the aliasing
    guard whose absence let the in/out memref segfault through `as`/`gdb`; the
    contrapositive is exactly `memrefPtrsDistinct_of_collapse_false` (a
    same-register lowering fails the decidable `Nodup` check). -/
theorem validate_memrefDistinct_two {virtBody : Lcmd} {fd : Lfundef} {tbl : Array Nat}
    {framePerSlot : Nat}
    (h : validateLfundefWith virtBody tbl fd 2 framePerSlot = true) :
    MemrefPtrsDistinct virtBody tbl := by
  have hB : memrefPtrsDistinctB virtBody tbl 2 = true := validate_memrefDistinctB h
  rw [memrefPtrsDistinctB_two_iff] at hB
  exact hB

/-! ### 5d. Clause (d) → semantic: every spill name resolves -/

/-- **Clause (d) soundness (bridged).** If a function passes the validator, every
    spill name referenced in its body parses to a concrete slot index — there is no
    `%<UNKNOWN:k.N>` unresolved-spill placeholder (bug class 3 on the spill side). A
    direct corollary of the `spillsResolved` conjunct. -/
theorem validate_spillsResolved {virtBody : Lcmd} {fd : Lfundef} {tbl : Array Nat}
    {nPtr framePerSlot : Nat}
    (h : validateLfundefWith virtBody tbl fd nPtr framePerSlot = true) :
    ∀ n ∈ allSpillNames (bodyInstrs fd), (spillSlotIndex n).isSome = true := by
  have hsc : spillConsistentB (bodyInstrs fd) fd.lfd_frame_size framePerSlot = true :=
    validate_spillConsistent h
  unfold spillConsistentB at hsc
  rw [Bool.and_eq_true] at hsc
  have hres : spillsResolved (bodyInstrs fd) = true := hsc.1
  unfold spillsResolved at hres
  intro n hn
  exact (List.all_eq_true.mp hres) n hn

/-! ### 5e. Clause (c): the argument-materialization decidable check, and the
explicit semantic-bridge goal

The decidable `argsMaterialized` check is discharged by the validator. Its
*semantic* form is the `argMatSeq_reads` premise — a statement about the prologue's
net `Lstate` effect establishing the body's argument registers. That bridge lives
*outside* the modeled straight-line fragment (the prologue uses the `MOVQ` mnemonic
`lsemStep` does not model; `toLprogPhysAbi_lsem` carries it as the explicit
`hProlog`/`hrel` hypotheses). We therefore state the decidable→semantic bridge as an
explicit named goal and prove the decidable direction the checker
gives. -/

/-- The decidable materialization fact the validator discharges: if a function
    passes, then for every SIB base `r` the body reads, `r` is materialized before
    its first use (`materializedBeforeUse`). The decidable witness of
    `argMatSeq_reads`'s premise. -/
theorem validate_argsMaterialized_decidable {virtBody : Lcmd} {fd : Lfundef}
    {tbl : Array Nat} {nPtr framePerSlot : Nat}
    (h : validateLfundefWith virtBody tbl fd nPtr framePerSlot = true) :
    ∀ r ∈ allSibBases (bodyInstrs fd), materializedBeforeUse (bodyInstrs fd) r = true := by
  have ham : argsMaterialized (bodyInstrs fd) = true := validate_argsMaterialized h
  unfold argsMaterialized at ham
  intro r hr
  exact (List.all_eq_true.mp ham) r hr

/-- **The explicit decidable→semantic bridge goal for clause (c)** (a stated
    `Prop`). The decidable `materializedBeforeUse` check (proved discharged above)
    should entail the *semantic* materialization premise of `argMatSeq_reads`: that
    there is a materialization pair list with fresh sources and distinct
    destinations (`SourcesFresh`/`DestsDistinct`) whose run establishes the argument
    registers (`argMat_establishes_argRegs`). Closing it requires the prologue's net
    `Lstate` model — the `hProlog`/`hrel` content `toLprogPhysAbi_lsem` carries
    explicitly, which is *outside* this module's straight-line fragment. We state it
    as the named obligation; the decidable direction is `validate_argsMaterialized_decidable`. -/
def validate_argMat_bridge_goal (fd : Lfundef) : Prop :=
  (∀ r ∈ allSibBases (bodyInstrs fd), materializedBeforeUse (bodyInstrs fd) r = true) →
    ∃ pairs : List (String × String), SourcesFresh pairs ∧ DestsDistinct pairs

/-! ### 5f. Whole-program soundness wrapper -/

/-- **Whole-program clause-(a) soundness.** If `validateLowering p = true`, every
    instruction of every function body satisfies the two assemble-legality
    properties `as` needs. The post-lowering gate's primary guarantee. -/
theorem validateLowering_sound_wf {p : Lprog} {virtFor : String → Lcmd × Array Nat}
    {nPtr framePerSlot : Nat}
    (h : validateLowering p virtFor nPtr framePerSlot = true) :
    ∀ e ∈ p.lp_funcs, ∀ i ∈ e.2.lfd_body,
      atMostOneMemOperand i.li_i ∧ allOperandsResolved i.li_i := by
  unfold validateLowering at h
  intro e he i hi
  have hfd := (List.all_eq_true.mp h) e he
  exact validate_wfLinstr_sound hfd i hi

/-- **Whole-program clause-(b) soundness (the KEY discharge).** If
    `validateLowering p virtFor 2 _ = true` for the two-pointer ABI, every function
    satisfies the semantic `MemrefPtrsDistinct` precondition of
    `toLprogPhysAbi_lsem` over its supplied virtual body+table — the in/out memref
    aliasing guard, discharged at lowering time. -/
theorem validateLowering_sound_memrefDistinct {p : Lprog}
    {virtFor : String → Lcmd × Array Nat} {framePerSlot : Nat}
    (h : validateLowering p virtFor 2 framePerSlot = true) :
    ∀ e ∈ p.lp_funcs, MemrefPtrsDistinct (virtFor e.1).1 (virtFor e.1).2 := by
  unfold validateLowering at h
  intro e he
  have hfd := (List.all_eq_true.mp h) e he
  exact validate_memrefDistinct_two hfd

/-- **Whole-program clause-(d) soundness.** If `validateLowering p = true`, every
    spill name in every body resolves to a concrete slot index — no `%<UNKNOWN>`
    unresolved spill. -/
theorem validateLowering_sound_spillsResolved {p : Lprog}
    {virtFor : String → Lcmd × Array Nat} {nPtr framePerSlot : Nat}
    (h : validateLowering p virtFor nPtr framePerSlot = true) :
    ∀ e ∈ p.lp_funcs, ∀ n ∈ allSpillNames (bodyInstrs e.2),
      (spillSlotIndex n).isSome = true := by
  unfold validateLowering at h
  intro e he n hn
  have hfd := (List.all_eq_true.mp h) e he
  exact validate_spillsResolved hfd n hn

/-! ## 6. Smoke tests: accept a good Lprog, reject the bug shapes

`native_decide` over concrete `Lprog`s: the validator ACCEPTS a good MontRedc /
MayoUov-shaped function and REJECTS each of the four bug shapes — `mem → mem`,
unresolved spill, aliased pointer args, un-materialized arg base. -/

/-- A small **good** function body: materialize the two argument pointers into body
    registers `RDI`/`RSI` (the prologue/materialization `mov`s), then a SIB load
    through the materialized base `RDI`, a binop, and a store through `RSI`. Every
    instruction is WF, the two pointers occupy distinct registers, and both bases
    are written before use. (MontRedc / MayoUov shape: load operand, compute,
    store.) -/
def goodBody : Lcmd :=
  [ ⟨0, .Lopn [.reg "RDI"] "MOV" [.reg "RDI"]⟩           -- materialize arg-base 0 (in ptr)
  , ⟨0, .Lopn [.reg "RSI"] "MOV" [.reg "RSI"]⟩           -- materialize arg-base 1 (out ptr)
  , ⟨0, .Lopn [.reg "RAX"] "MOV" [.arrIdx "RDI" "RCX" 8]⟩ -- load [RDI + RCX*8]
  , ⟨0, .Lopn [.reg "RAX"] "ADD:64" [.reg "RAX", .reg "RDX"]⟩ -- compute
  , ⟨0, .Lopn [.reg "RSI"] "MOV" [.reg "RAX"]⟩ ]          -- store to out reg

/-- A good function: two pointer args, the `goodBody`, a frame that covers its (zero)
    spills. -/
def goodFundef : Lfundef :=
  { lfd_arg := ["a0", "a1"], lfd_body := goodBody, lfd_frame_size := 64 }

/-- The **virtual** (pre-RA) body for clause (b): the two pointer args `argName 0`
    (`"a0"`) and `argName 1` (`"a1"`) both appear (read together in one op, so they
    are simultaneously live and the allocator must give them distinct physical
    registers). Over this body + its own `physTable`, `memrefPtrsDistinctB … 2` is
    `true` — the good (non-aliased) lowering. -/
def goodVirtBody : Lcmd :=
  [ ⟨0, .Lopn [.reg "r0"] "ADD:64" [.reg (argName 0), .reg (argName 1)]⟩ ]

/-- The clause-(b) input pair for the good function: its virtual body and the
    physical-rename table derived from it. -/
def goodVirt : Lcmd × Array Nat :=
  (goodVirtBody, physTable (bodyTrace goodVirtBody))

/-- A **bug-1 (`mem → mem`)** body: a `mov` with two spill (memory) operands — the
    illegal two-memory `mov` `as` rejects. `wfLinstr` (clause a) flags it. -/
def memToMemBody : Lcmd :=
  [ ⟨0, .Lopn [.reg "k.0"] "MOV" [.reg "k.1"]⟩ ]

def memToMemFundef : Lfundef :=
  { lfd_arg := ["a0"], lfd_body := memToMemBody, lfd_frame_size := 64 }

/-- A **bug-3 (unresolved spill)** body: a spill name `k.x` whose `<n>` is not a
    parseable nat — the `%<UNKNOWN>` sentinel. `opResolved` (clause a) and
    `spillsResolved` (clause d) both flag it. -/
def unresolvedSpillBody : Lcmd :=
  [ ⟨0, .Lopn [.reg "RAX"] "MOV" [.reg "k.x"]⟩ ]

def unresolvedSpillFundef : Lfundef :=
  { lfd_arg := ["a0"], lfd_body := unresolvedSpillBody, lfd_frame_size := 64 }

/-- An **un-materialized arg base** body: it reads `[RDI + RCX*8]` as a SIB base
    *without* first writing `RDI` — the un-materialized-pointer segfault. Clause (c)
    `argsMaterialized` flags it (`firstWriteIdx` is `none`). -/
def unmaterializedBody : Lcmd :=
  [ ⟨0, .Lopn [.reg "RAX"] "MOV" [.arrIdx "RDI" "RCX" 8]⟩ ]  -- reads RDI base, never written

def unmaterializedFundef : Lfundef :=
  { lfd_arg := ["a0"], lfd_body := unmaterializedBody, lfd_frame_size := 64 }

/-- The decidable distinctness check, exposed directly over the **image name
    list** (the form `memrefPtrsDistinctB` reduces to after the rename map): the
    pointer arguments' physical names are `Nodup`. An aliased lowering produces a
    list with a duplicate physical name. This is the fully-reducible core of clause
    (b), so the aliasing rejection is a plain `decide`/`native_decide` rather than
    going through the opaque `nameSlot`. -/
def physNamesNodup (names : List String) : Bool := names.Nodup

/-- The image-name list of an **aliased** two-pointer lowering: both pointers map
    to the same physical register `"RDI"` (the in/out memref aliasing bug —
    `physRename body tbl (argName 0) = physRename body tbl (argName 1)`). -/
def aliasedPtrNames : List String := ["RDI", "RDI"]

/-- The image-name list of a **good** two-pointer lowering: distinct physical
    registers. -/
def distinctPtrNames : List String := ["RDI", "RSI"]

/-! ### Accept -/

-- Clause (b) on the good virtual body: the two pointer args resolve distinct.
example : memrefPtrsDistinctB goodVirtBody (physTable (bodyTrace goodVirtBody)) 2 = true := by
  native_decide

-- The good function is ACCEPTED (good virtual body for clause b, 2 pointers,
-- 8-byte slots).
example :
    validateLfundefWith goodVirtBody (physTable (bodyTrace goodVirtBody)) goodFundef 2 8
      = true := by
  native_decide

-- The good whole program is ACCEPTED (the lowering supplies `goodVirt` for every
-- function name).
example :
    validateLowering { lp_funcs := [("f", goodFundef)] } (fun _ => goodVirt) 2 8 = true := by
  native_decide

/-! ### Reject -/

-- For the single-pointer reject shapes, clause (b) is trivially satisfied (a
-- 1-element name list is `Nodup`); the rejection comes from clause (a)/(c)/(d).
-- We use the physical body itself as the (degenerate) virtual body for clause (b).

-- Bug 1 (`mem → mem`): REJECTED by clause (a) `wfLfundef`.
example :
    validateLfundefWith memToMemBody (physTable (bodyTrace memToMemBody))
      memToMemFundef 1 8 = false := by
  native_decide

-- Bug 3 (unresolved spill): REJECTED by clauses (a)/(d).
example :
    validateLfundefWith unresolvedSpillBody (physTable (bodyTrace unresolvedSpillBody))
      unresolvedSpillFundef 1 8 = false := by
  native_decide

-- Un-materialized arg base: REJECTED by clause (c) `argsMaterialized`.
example :
    validateLfundefWith unmaterializedBody (physTable (bodyTrace unmaterializedBody))
      unmaterializedFundef 1 8 = false := by
  native_decide

-- Standalone clause-(c) rejection of the un-materialized base.
example : argsMaterialized (bodyInstrs unmaterializedFundef) = false := by native_decide

-- Aliased pointer args on one register: the decidable distinctness core REJECTS
-- (both pointers map to "RDI" — a duplicate in the image name list).
example : physNamesNodup aliasedPtrNames = false := by native_decide

-- A good (distinct) two-pointer lowering PASSES the distinctness core.
example : physNamesNodup distinctPtrNames = true := by native_decide

-- `memrefPtrsDistinctB` is exactly `physNamesNodup` on the rename image — so the
-- aliasing rejection above transfers to the real clause once the rename image is
-- the aliased list.
example (body : Lcmd) (tbl : Array Nat) (nPtr : Nat) :
    memrefPtrsDistinctB body tbl nPtr
      = physNamesNodup ((ptrArgNames nPtr).map (physRename body tbl)) := rfl

-- A directly-collapsing renaming (both arg names → the same physical name) fails
-- the distinctness clause: this is the `memrefPtrsDistinct_of_collapse_false` shape.
example (body : Lcmd) (tbl : Array Nat)
    (hcollapse : physRename body tbl (argName 0) = physRename body tbl (argName 1)) :
    memrefPtrsDistinctB body tbl 2 = false := by
  cases hb : memrefPtrsDistinctB body tbl 2
  · rfl
  · rw [memrefPtrsDistinctB_two_iff] at hb
    exact absurd hcollapse hb

end CatCrypt.Crypto.SecureCompilation.X86Backend.ValidateLowering
