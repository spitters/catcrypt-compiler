/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulSpill

/-!
# `toLprogPhysAbi` faithfulness — the RA store-relation WRITE side

`ToLprogFaithfulSpill.evalOperand_remapOperand_reg` proves the **read** side of
the linear-scan RA refinement: under a store relation

  `hrel : ∀ m, s'.lvm (physRename body tbl m) = s.lvm m`

evaluating a `remapOperand`-renamed register operand against the physical store
`s'` equals evaluating the original against the virtual store `s`. That lemma is
stated *relative to* the relation; it does not say the relation is
**maintained** across a write. This module discharges the write side: after a
`legalizeBinop`-emitted binding executes under `lsemStraight`, the store relation
is **re-established** for the next binding.

## The relation is indexed by a live set

Write `ρ := physRename body tbl` (the physical RA renaming, §4 of `…Spill`). The
store relation between a virtual store `s` and a physical store `s'` carries a
list `L` of logical names — the names live at the program point it holds at:

  `StoreRel body tbl L s s' := ∀ m ∈ L, s'.lvm (ρ m) = s.lvm m`.

Quantifying over `L` rather than over all strings is what makes the relation
satisfiable at a shipped allocation. `ρ` is not injective: a linear-scan
allocator reuses one physical register across logical names whose live ranges
are disjoint, and it sends every name the body does not mention to a single
sentinel location (`ToLprogFaithfulBinopMov.physRename_eq_of_not_mem`). A
relation quantified over all names therefore equates the virtual values of names
that share a register, which no execution satisfies. Restricted to the names
live at one point, it is the agreement a register allocation preserves.

## The virtual step and the physical step

A virtual binop binding writes its logical destination `nDst` with the result
`v`, i.e. the virtual store steps `s ↦ s.setReg nDst v`. On the physical side the
same binding is realised as `legalizeBinop (.reg (ρ nDst)) (.reg (ρ nSrc)) opn`,
which (by `legalizeBinop_lsem`) writes `v` at `ρ nDst` — but, in the spill
branches, **also** writes the scratches `R15`/`R14`.

## The dead-scratch invariant (stated precisely, and discharged)

Maintenance holds **modulo the scratches**: `R15`/`R14` are written transiently
inside `legalizeBinop` but are *dead between bindings* — they are **not in the
image of `ρ`**, so a write to them is invisible to `StoreRel`. We state this as

  `physRename_ne_reloadScratch  : ∀ m, ρ m ≠ reloadScratch`
  `physRename_ne_reloadScratch2 : ∀ m, ρ m ≠ reloadScratch2`

and discharge both: `ρ m = physRegName (physMapTabled tbl (nameSlot body m))`,
and `physRegName` only ever emits one of the 13 GP names `RAX…R13` or a `k.N`
spill name — never `R15`/`R14`.

## The four side conditions of the step

`legalizeBinop_storeRel_step` carries a live set `Lin` before the binding and a
live set `Lout` after it, related by four conditions:

* `hdstIn : nDst ∈ Lin` and `hsrcIn : nSrc ∈ Lin` — the binding reads both of
  its operands, so both are live on entry and the read relation covers them;
* `hinj : ∀ m ∈ Lout, ρ m = ρ nDst → m = nDst` — the destination's physical
  register is not shared with any *other* name live after the binding. This is
  the interference condition of the allocation at this program point, in the
  shape `JasminLprogExport.InterferenceRespected` states it: the defined name
  together with the live-out set, pairwise distinct under `ρ`. Restricting it to
  `Lout` is what a slot-reducing allocation can satisfy; the same condition
  quantified over all strings holds at no binding of a shipped kernel, because
  the sentinel fibre alone already refutes it;
* `hcarry : ∀ m ∈ Lout, m ≠ nDst → m ∈ Lin` — every name live after the binding
  other than the one it defines was already live before it, so the write-frame
  carries its value across.

`hinj` and `hcarry` are properties of the register allocation and of the
liveness of the source program. They are hypotheses here, not derived from the
allocator: `ToLprogFaithfulRA.physRename_injOn_live` reduces `hinj` to
slot-level injectivity on the live set and `ToLprogFaithfulRA.physMap_no_collision`
supplies that for slots whose live ranges overlap, but the two facts about the
`Lcmd` layer that join them — the `physTable`-scatter agreement and the
binding-position-to-`physLiveRange` correspondence — are the named residual of
that module.

## What this module proves vs the residual

PROVED (against the real `lsemStraight`):
* `legalizeBinop_writeFrame`: `legalizeBinop` leaves every register **outside**
  `{dst, R15, R14}` unchanged (the write-frame of all four branches);
* `physRename_ne_reloadScratch{,2}`: the scratches are out of `ρ`'s image;
* `legalizeBinop_storeRel_step`: the per-binding maintenance — `StoreRel` at
  `Lout` is re-established after one `legalizeBinop` binding, given the read
  relation at `Lin`, the dead-scratch facts (discharged), and the four side
  conditions above.

The whole-body threading of these steps is the sibling
`ToLprogFaithfulBody.physBlocks_storeRel`; the leading two-address
`mov dst, s0` per binding for `dst ≠ s0` is packaged as a `BlockMaintains`
witness in `ToLprogFaithfulTwoAddr`.

RESIDUAL (NOT proved here):
* the interference condition `hinj` and the liveness condition `hcarry`, as
  described above;
* `arr`/`arrIdx` (memory) operands: `remapOperand` passes them through unrenamed,
  so their maintenance is a `StoreAgreesM` (memory) obligation, not this register
  relation;
* the ABI prologue/epilogue and the `Lret` terminator (control flow, outside
  `lsemStraight`'s straight-line scope — `lsemStep .Lret = none`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulWriteSide

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulSpill

/-! ## 0. The dead-scratch invariant: `R15`/`R14` are out of `ρ`'s image

`ρ m = physRegName (physMapTabled tbl (nameSlot body m))`, and `physRegName`
emits only a GP name `RAX…R13` (none is `R15`/`R14`) or a `k.N` spill name. So no
physical name `ρ m` is ever a scratch. -/

set_option maxRecDepth 4000 in
/-- `physRegName` never produces the primary scratch `R15`: its output is a GP
    register name (`RAX…R13`), an `XMM`/`kv.N` vector name, or a `k.N` spill
    name. -/
theorem physRegName_ne_reloadScratch (phys : Nat) :
    physRegName phys ≠ reloadScratch := by
  unfold physRegName reloadScratch
  split
  · simp only []
    cases h : vectorRegNames[phys - vectorBase]? with
    | none =>
      intro hk
      have hd := congrArg String.toList hk
      rw [String.toList_append] at hd
      simp [show "kv.".toList = ['k', 'v', '.'] from rfl,
        show "R15".toList = ['R', '1', '5'] from rfl] at hd
    | some r =>
      have hmem : r ∈ vectorRegNames := List.mem_of_getElem? h
      intro hr; subst hr; revert hmem; decide
  · cases h : gpRegNames[phys]? with
    | none =>
      intro hk
      have hd := congrArg String.toList hk
      rw [String.toList_append] at hd
      simp [show "k.".toList = ['k', '.'] from rfl,
        show "R15".toList = ['R', '1', '5'] from rfl] at hd
    | some r =>
      have hmem : r ∈ gpRegNames := List.mem_of_getElem? h
      intro hr; subst hr; revert hmem; decide

set_option maxRecDepth 4000 in
/-- `physRegName` never produces the secondary scratch `R14`. -/
theorem physRegName_ne_reloadScratch2 (phys : Nat) :
    physRegName phys ≠ reloadScratch2 := by
  unfold physRegName reloadScratch2
  split
  · simp only []
    cases h : vectorRegNames[phys - vectorBase]? with
    | none =>
      intro hk
      have hd := congrArg String.toList hk
      rw [String.toList_append] at hd
      simp [show "kv.".toList = ['k', 'v', '.'] from rfl,
        show "R14".toList = ['R', '1', '4'] from rfl] at hd
    | some r =>
      have hmem : r ∈ vectorRegNames := List.mem_of_getElem? h
      intro hr; subst hr; revert hmem; decide
  · cases h : gpRegNames[phys]? with
    | none =>
      intro hk
      have hd := congrArg String.toList hk
      rw [String.toList_append] at hd
      simp [show "k.".toList = ['k', '.'] from rfl,
        show "R14".toList = ['R', '1', '4'] from rfl] at hd
    | some r =>
      have hmem : r ∈ gpRegNames := List.mem_of_getElem? h
      intro hr; subst hr; revert hmem; decide

/-- **Dead-scratch invariant, primary.** No physical RA name `ρ m =
    physRename body tbl m` aliases the primary scratch `R15`. -/
theorem physRename_ne_reloadScratch (body : Lcmd) (tbl : Array Nat) (m : String) :
    physRename body tbl m ≠ reloadScratch :=
  physRegName_ne_reloadScratch _

/-- **Dead-scratch invariant, secondary.** No physical RA name aliases `R14`. -/
theorem physRename_ne_reloadScratch2 (body : Lcmd) (tbl : Array Nat) (m : String) :
    physRename body tbl m ≠ reloadScratch2 :=
  physRegName_ne_reloadScratch2 _

/-! ## 1. The write-frame of `legalizeBinop`

Every emitted `Lopn` writes a single destination, and across all four spill
branches the destinations are confined to `{dst, R15, R14}`. So a register `y`
outside that set is left unchanged by the whole sequence. We prove this from a
generic single-`Lopn` frame and a cons-inversion of `lsemStraight`. -/

/-- **Single-`Lopn` write-frame.** A successful `Lopn [reg d] o args` step leaves
    every register `y ≠ d` unchanged: it writes `d` only and advances the pc. -/
theorem lsemStep_Lopn_frame {w : Nat} (d o : String) (args : List LOperand)
    (s s' : Lstate w)
    (hstep : lsemStep (.Lopn [.reg d] o args) s = some s') (y : String) (hy : y ≠ d) :
    s'.lvm y = s.lvm y := by
  simp only [lsemStep] at hstep
  split at hstep <;> (repeat' split at hstep) <;>
    simp_all [Lstate.setReg, Lstate.nextPc]
  all_goals (rw [← hstep] <;> simp [hy])

/-- Cons-inversion of a successful straight-line run: the head steps to some
    intermediate state from which the tail runs to the final state. -/
theorem lsemStraight_cons_inv {w : Nat} (i : LinstrR) (is : List LinstrR)
    (s s' : Lstate w) (h : lsemStraight (i :: is) s = some s') :
    ∃ s1, lsemStep i s = some s1 ∧ lsemStraight is s1 = some s' := by
  rw [lsemStraight_cons] at h
  cases hi : lsemStep i s with
  | none => rw [hi] at h; exact absurd h (by simp)
  | some s1 => rw [hi] at h; exact ⟨s1, rfl, h⟩

/-- **`legalizeBinop` write-frame (all four branches).** Running
    `legalizeBinop (.reg dst) (.reg src) opn` under `lsemStraight` leaves every
    register `y` **outside** `{dst, R15, R14}` unchanged. The three scratch
    exclusions cover the spill branches (which transiently write `R15`/`R14`);
    `y ≠ dst` covers the final destination write. No `applyOpn`/freshness premise
    is needed — the frame holds whenever the run *succeeds* (the `some s'`
    hypothesis), regardless of the binop's value. -/
theorem legalizeBinop_writeFrame {w : Nat} (s s' : Lstate w) (dst src opn : String)
    (y : String) (hy : y ≠ dst) (hy15 : y ≠ reloadScratch) (hy14 : y ≠ reloadScratch2)
    (hrun : lsemStraight (legalizeBinop (.reg dst) (.reg src) opn "MOV") s = some s') :
    s'.lvm y = s.lvm y := by
  unfold legalizeBinop at hrun
  rcases hd : (LOperand.reg dst).isSpill <;> rcases hs : (LOperand.reg src).isSpill <;>
    simp only [hd, hs] at hrun
  · -- (false, false): `op dst, src`
    obtain ⟨s1, h1, htl⟩ := lsemStraight_cons_inv _ _ _ _ hrun
    rw [lsemStraight_nil] at htl; obtain rfl := Option.some.inj htl
    exact lsemStep_Lopn_frame _ _ _ _ _ h1 y hy
  · -- (false, true): `mov R15, src ; op dst, R15`
    obtain ⟨s1, h1, htl⟩ := lsemStraight_cons_inv _ _ _ _ hrun
    obtain ⟨s2, h2, htl⟩ := lsemStraight_cons_inv _ _ _ _ htl
    rw [lsemStraight_nil] at htl; obtain rfl := Option.some.inj htl
    rw [lsemStep_Lopn_frame _ _ _ _ _ h2 y hy,
        lsemStep_Lopn_frame _ _ _ _ _ h1 y hy15]
  · -- (true, false): `mov R15, dst ; op R15, src ; mov dst, R15`
    obtain ⟨s1, h1, htl⟩ := lsemStraight_cons_inv _ _ _ _ hrun
    obtain ⟨s2, h2, htl⟩ := lsemStraight_cons_inv _ _ _ _ htl
    obtain ⟨s3, h3, htl⟩ := lsemStraight_cons_inv _ _ _ _ htl
    rw [lsemStraight_nil] at htl; obtain rfl := Option.some.inj htl
    rw [lsemStep_Lopn_frame _ _ _ _ _ h3 y hy,
        lsemStep_Lopn_frame _ _ _ _ _ h2 y hy15,
        lsemStep_Lopn_frame _ _ _ _ _ h1 y hy15]
  · -- (true, true): `mov R15, dst ; mov R14, src ; op R15, R14 ; mov dst, R15`
    obtain ⟨s1, h1, htl⟩ := lsemStraight_cons_inv _ _ _ _ hrun
    obtain ⟨s2, h2, htl⟩ := lsemStraight_cons_inv _ _ _ _ htl
    obtain ⟨s3, h3, htl⟩ := lsemStraight_cons_inv _ _ _ _ htl
    obtain ⟨s4, h4, htl⟩ := lsemStraight_cons_inv _ _ _ _ htl
    rw [lsemStraight_nil] at htl; obtain rfl := Option.some.inj htl
    rw [lsemStep_Lopn_frame _ _ _ _ _ h4 y hy,
        lsemStep_Lopn_frame _ _ _ _ _ h3 y hy15,
        lsemStep_Lopn_frame _ _ _ _ _ h2 y hy14,
        lsemStep_Lopn_frame _ _ _ _ _ h1 y hy15]

/-! ## 2. The store relation and its per-binding maintenance

`StoreRel body tbl L s s'` is the read relation `evalOperand_remapOperand_reg`
consumes, restricted to a live set: at every name `m` of `L`, the physical store
`s'` reads at the renamed register `ρ m` what the virtual store `s` reads at `m`.
The maintenance theorem `legalizeBinop_storeRel_step` carries it from the live-in
set of one `legalizeBinop` binding to the live-out set. -/

/-- The RA store relation along the physical renaming `ρ = physRename body tbl`,
    at the live set `L`: the physical store `s'` agrees with the virtual store
    `s`, read through `ρ`, at every logical name of `L`. `L` is the set of names
    live at the program point the relation holds at; `ρ` is injective on no
    larger set, since the allocator reuses a register across names with disjoint
    live ranges. -/
def StoreRel {w : Nat} (body : Lcmd) (tbl : Array Nat) (L : List String)
    (s s' : Lstate w) : Prop :=
  ∀ m ∈ L, s'.lvm (physRename body tbl m) = s.lvm m

/-- **Per-binding store-relation maintenance (the write side).** Suppose the read
    relation `StoreRel body tbl Lin s s'` holds at the live-in set `Lin` before a
    binop binding whose logical destination is `nDst` and whose two sources are
    `nDst`, `nSrc`. On the virtual side the binding steps `s ↦ s.setReg nDst v`
    (with `v` the binop result). On the physical side it is realised as
    `legalizeBinop (.reg (ρ nDst)) (.reg (ρ nSrc)) opn` (`ρ = physRename body
    tbl`). Then that physical sequence runs to a state `s''` for which the store
    relation is **re-established** at the live-out set `Lout`:
    `StoreRel body tbl Lout (s.setReg nDst v) s''`.

    The ingredients:
    * the read relation at the two operands (`hdstIn`, `hsrcIn` place them in
      `Lin`) gives `s'.lvm (ρ nDst) = s.lvm nDst` and likewise for `nSrc`, so the
      physical binop computes the same `v` (`legalizeBinop_lsem`);
    * the **dead-scratch invariant** (`physRename_ne_reloadScratch{,2}`, discharged
      here) excludes `R15`/`R14` from `ρ`'s image, so the transient scratch writes
      of the spill branches are invisible to the relation (via
      `legalizeBinop_writeFrame`);
    * the **live-out interference condition** `hinj : ∀ m ∈ Lout, ρ m = ρ nDst →
      m = nDst` confines the physical write at `ρ nDst` to exactly the `nDst`
      fibre among the names live after the binding, matching the virtual
      `setReg nDst`. A name that shares `nDst`'s register but is dead here is
      unconstrained, which is what lets a slot-reducing allocation satisfy it;
    * the **live-out carry condition** `hcarry : ∀ m ∈ Lout, m ≠ nDst → m ∈ Lin`
      routes every other live-out name back through the incoming relation.

    `hinj` and `hcarry` are conditions on the register allocation and on the
    liveness of the source program; see the module docstring. This is the
    single-binding step; the whole-`physBody` threading is
    `ToLprogFaithfulBody.physBlocks_storeRel`. -/
theorem legalizeBinop_storeRel_step {w : Nat} (body : Lcmd) (tbl : Array Nat)
    (Lin Lout : List String) (s s' : Lstate w) (nDst nSrc opn : String)
    (hrel : StoreRel body tbl Lin s s')
    (hdstIn : nDst ∈ Lin) (hsrcIn : nSrc ∈ Lin)
    (hinj : ∀ m ∈ Lout, physRename body tbl m = physRename body tbl nDst → m = nDst)
    (hcarry : ∀ m ∈ Lout, m ≠ nDst → m ∈ Lin)
    (hstrip : stripWidthTag opn = opn) (v : BitVec w)
    (hop : applyOpn opn [s.lvm nDst, s.lvm nSrc] = some v) :
    ∃ s'', lsemStraight
        (legalizeBinop (.reg (physRename body tbl nDst))
          (.reg (physRename body tbl nSrc)) opn "MOV") s' = some s''
      ∧ StoreRel body tbl Lout (s.setReg nDst v) s'' := by
  unfold StoreRel at hrel ⊢
  have hreadD : s'.lvm (physRename body tbl nDst) = s.lvm nDst := hrel nDst hdstIn
  have hreadS : s'.lvm (physRename body tbl nSrc) = s.lvm nSrc := hrel nSrc hsrcIn
  have hop' : applyOpn opn
      [s'.lvm (physRename body tbl nDst), s'.lvm (physRename body tbl nSrc)] = some v := by
    rw [hreadD, hreadS]; exact hop
  obtain ⟨s'', hrun, hval⟩ := legalizeBinop_lsem s'
    (physRename body tbl nDst) (physRename body tbl nSrc) opn
    (physRename_ne_reloadScratch body tbl nDst)
    (Ne.symm (physRename_ne_reloadScratch body tbl nSrc))
    reloadScratch_ne_reloadScratch2 hstrip v hop'
  refine ⟨s'', hrun, ?_⟩
  intro m hmL
  by_cases hm : physRename body tbl m = physRename body tbl nDst
  · -- `m` shares `nDst`'s slot and is live out ⇒ `m = nDst`; both sides are `v`.
    have hmd : m = nDst := hinj m hmL hm
    subst hmd
    rw [hval]
    simp [Lstate.setReg]
  · -- `m`'s slot differs from `nDst`'s ⇒ frame + read relation, and `m ≠ nDst`.
    have hframe : s''.lvm (physRename body tbl m) = s'.lvm (physRename body tbl m) :=
      legalizeBinop_writeFrame s' s''
        (physRename body tbl nDst) (physRename body tbl nSrc) opn
        (physRename body tbl m) hm
        (physRename_ne_reloadScratch body tbl m) (physRename_ne_reloadScratch2 body tbl m) hrun
    have hmne : m ≠ nDst := fun he => hm (by rw [he])
    rw [hframe, hrel m (hcarry m hmL hmne)]
    simp [Lstate.setReg, hmne]

end CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulWriteSide
