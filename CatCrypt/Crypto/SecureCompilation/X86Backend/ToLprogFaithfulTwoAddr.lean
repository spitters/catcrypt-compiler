/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulBody

/-!
# `lowerTwoAddr` faithfulness — the leading two-address `mov dst, s0` (`dst ≠ s0`)

`ToLprogFaithfulBody.binopBlockMaintains` packages the per-binding write-side
step for the **two-address collapse** case `dst = s0`: the RA placed `dst` on
`s0`'s register, so `lowerTwoAddr` emits exactly `legalizeBinop dst s1 opn` and
the block is the bare legalized binop. This module discharges the **named
residual** from that file's docstring: when `dst ≠ s0`, `lowerTwoAddr` prepends
a leading `mov dst, s0` (itself legalized) before the binop:

  `lowerTwoAddr dst s0 s1 opn "MOV" = legalizeMov dst s0 "MOV" ++ legalizeBinop dst s1 opn "MOV"`

(the `materializeWideImm` prelude is empty on the default `"MOV"` path,
`materializeWideImm_MOV`). We prove this whole sequence re-establishes
`StoreRel` and package it as a `BlockMaintains` witness, so bodies with
`dst ≠ s0` bindings thread end-to-end exactly like the `dst = s0` bodies.

## How the leading `mov` composes with the binop step

The leading `mov ρdst, ρs0` copies `s'.lvm (ρ s0)` into `ρ dst`. On the
**virtual** side the matching transformer is the intermediate copy
`sMid := s.setReg nDst (s.lvm nS0)` — the moved value lands logically at `nDst`.
We show (`legalizeMov_regReg_storeRel_step`) that the leading mov re-establishes
`StoreRel body tbl sMid s'2` from `StoreRel body tbl s s'`, by the **same**
dead-scratch + destination-injectivity argument as the binop write-side step
(`legalizeBinop_storeRel_step`): the mov writes only `ρ dst`, and injectivity
confines that write to the `nDst` fibre.

Then the subsequent `legalizeBinop ρdst ρs1 opn` runs on `(sMid, s'2)` exactly as
`legalizeBinop_storeRel_step` requires, with the two binop sources `[nDst, nS1]`.
Because `sMid.lvm nDst = s.lvm nS0` (the just-moved value) and
`sMid.lvm nS1 = s.lvm nS1` (when `nS1 ≠ nDst`), and `sMid.setReg nDst v =
s.setReg nDst v` (the second write overwrites the copy), the composed virtual
transformer is

  `s ↦ s.setReg nDst (applyOpn opn [s.lvm nS0, s.lvm nS1])`

— the two-address denotation reading `s0` as the first binop operand.

## What this module proves vs the residual

PROVED (against the real `lsemStraight`):
* `legalizeMov_regReg_step`: the single-step effect of the leading
  no-spill `mov dst, s0` (`legalizeMov`'s non-spill branch) under `lsemStraight`;
* `legalizeMov_regReg_storeRel_step`: that leading mov re-establishes `StoreRel`
  against the virtual copy `s ↦ s.setReg nDst (s.lvm nS0)` (dead-scratch + `hinj`);
* `movThenBinop_storeRel_step`: the **composition** — the full `dst ≠ s0`
  `lowerTwoAddr` block (leading mov ++ legalized binop, both register-named)
  re-establishes `StoreRel` against the composed two-address virtual write;
* `movBinopBlockMaintains`: that composition packaged as a `BlockMaintains`
  witness, so `dst ≠ s0` bindings slot into `physBlocks_storeRel`'s whole-body
  threading exactly like the `dst = s0` `binopBlockMaintains`.

RESIDUAL (named honestly — NOT proved here):
* the **spilled leading mov** (`legalizeMov`'s `dst.isSpill && s0.isSpill`
  branch: `mov R15, s0; mov dst, R15`): in the shipped pipeline `physRegName`
  never both-spills `dst` and `s0` into the same scratch, but the two-`Lopn`
  reload variant is a separate write-frame composition not packaged here. The
  no-spill leading mov (the common case) is the one proved.
* the `materializeWideImm` U64 prelude (the `"MOV:64"` path): only the default
  `"MOV"` path (empty prelude) is covered; the wide-immediate reload through
  `R14` is out of scope.
* identifying the `physBody` `flatMap` output with the block list, `arr`/`arrIdx`
  memory operands, the ABI prologue/epilogue and `Lret` — exactly the residuals
  inherited from `ToLprogFaithfulBody` / `ToLprogFaithfulWriteSide`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulTwoAddr

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulSpill
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulWriteSide
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulBody

/-! ## 1. The leading no-spill `mov dst, s0`: single-step effect

`legalizeMov dst s0 "MOV"` on register-named operands (neither a spill) is the
single `Lopn [.reg dst] "MOV" [.reg s0]`. Under `lsemStraight` it copies
`s.lvm s0` into `dst` and advances the pc. -/

/-- **Leading no-spill `mov dst, s0`, single step.** Running the non-spill
    `legalizeMov (.reg dst) (.reg s0) "MOV"` (the single `mov dst, s0`) under
    `lsemStraight` writes `s.lvm s0` at `dst`: it runs to `(s.setReg dst
    (s.lvm s0)).nextPc`. No freshness premise — a copy reads `s0` once and writes
    `dst` once. (Hypothesis `hdsp`/`hssp`: the non-spill branch of `legalizeMov`,
    which fires when not both operands are spills — in particular when `dst` is a
    register.) -/
theorem legalizeMov_regReg_step {w : Nat} (s : Lstate w) (dst s0 : String)
    (hns : ¬ ((LOperand.reg dst).isSpill && (LOperand.reg s0).isSpill) = true) :
    lsemStraight (legalizeMov (.reg dst) (.reg s0) "MOV") s
      = some ((s.setReg dst (s.lvm s0)).nextPc) := by
  unfold legalizeMov
  rw [if_neg hns]
  have hstep : lsemStep (LinstrR.Lopn [.reg dst] "MOV" [.reg s0]) s
      = some ((s.setReg dst (s.lvm s0)).nextPc) := by
    simp only [lsemStep, List.map_cons, List.map_nil, evalOperand,
      ToLprogFaithfulProbe.stripWidthTag_MOV, applyOpn]
  simp only [lsemStraight_cons, hstep, lsemStraight_nil]

/-! ## 2. The leading `mov`: store-relation maintenance

The leading `mov ρdst, ρs0` writes only `ρ dst`, so the dead-scratch invariant is
not even needed (no scratch is touched); the destination-injectivity `hinj`
confines the physical write at `ρ nDst` to the `nDst` fibre, matching the virtual
copy `s ↦ s.setReg nDst (s.lvm nS0)`. -/

/-- **Leading no-spill `mov`, store-relation maintenance.** From the read relation
    `StoreRel body tbl s s'`, the leading `legalizeMov (.reg (ρ nDst)) (.reg
    (ρ nS0)) "MOV"` runs to some `s'2` re-establishing `StoreRel body tbl
    (s.setReg nDst (s.lvm nS0)) s'2`. The virtual side is the **copy** of `nS0`'s
    value into `nDst`. The destination injectivity `hinj` (the RA-correctness
    property — distinct live names get distinct slots) confines the physical write
    at `ρ nDst` to exactly the `nDst` fibre; every other renamed name is framed
    out by `lsemStep_Lopn_frame` and reads through `StoreRel`. -/
theorem legalizeMov_regReg_storeRel_step {w : Nat} (body : Lcmd) (tbl : Array Nat)
    (s s' : Lstate w) (nDst nS0 : String)
    (hrel : StoreRel body tbl s s')
    (hinj : ∀ m, physRename body tbl m = physRename body tbl nDst → m = nDst)
    (hns : ¬ ((LOperand.reg (physRename body tbl nDst)).isSpill
        && (LOperand.reg (physRename body tbl nS0)).isSpill) = true) :
    ∃ s'2, lsemStraight
        (legalizeMov (.reg (physRename body tbl nDst))
          (.reg (physRename body tbl nS0)) "MOV") s' = some s'2
      ∧ StoreRel body tbl (s.setReg nDst (s.lvm nS0)) s'2 := by
  unfold StoreRel at hrel ⊢
  -- The physical mov copies `s'.lvm (ρ nS0)` into `ρ nDst`; by the read relation
  -- `s'.lvm (ρ nS0) = s.lvm nS0`, the value being copied.
  have hrun := legalizeMov_regReg_step s'
    (physRename body tbl nDst) (physRename body tbl nS0) hns
  refine ⟨_, hrun, ?_⟩
  intro m
  by_cases hm : physRename body tbl m = physRename body tbl nDst
  · -- `m` shares `nDst`'s slot ⇒ `m = nDst`; both sides are the moved value.
    have hmd : m = nDst := hinj m hm
    subst hmd
    simp only [Lstate.lvm_nextPc, Lstate.lvm_setReg, if_pos]
    exact hrel nS0
  · -- `m`'s slot differs ⇒ the physical write at `ρ nDst` misses it (frame), and
    -- the virtual copy at `nDst` misses `m` (`m ≠ nDst`); read through `StoreRel`.
    simp only [Lstate.lvm_nextPc, Lstate.lvm_setReg, if_neg hm]
    have hmne : m ≠ nDst := fun he => hm (by rw [he])
    rw [if_neg hmne, hrel m]

/-! ## 3. The composition: the whole `dst ≠ s0` `lowerTwoAddr` block

`lowerTwoAddr (.reg (ρ nDst)) (.reg (ρ nS0)) (.reg (ρ nS1)) opn "MOV"` with
`ρ nDst ≠ ρ nS0` is `legalizeMov ρdst ρs0 ++ legalizeBinop ρdst ρs1 opn`
(the `materializeWideImm` prelude is empty on `"MOV"`). We peel it with
`lsemStraight_append`: the leading mov re-establishes `StoreRel` against the copy
`sMid := s.setReg nDst (s.lvm nS0)`, then `legalizeBinop_storeRel_step` runs on
`(sMid, s'2)` with sources `[nDst, nS1]`. Since `sMid.lvm nDst = s.lvm nS0` and
`sMid.lvm nS1 = s.lvm nS1` (`nS1 ≠ nDst`), and the binop's `setReg nDst`
overwrites the copy (`sMid.setReg nDst v = s.setReg nDst v`), the composed virtual
write is `s ↦ s.setReg nDst (applyOpn opn [s.lvm nS0, s.lvm nS1])`. -/

/-- **The `dst ≠ s0` two-address block, store-relation maintenance (composition).**
    The full leading-mov-then-binop block (both operand families register-named,
    leading mov non-spill) re-establishes `StoreRel` against the two-address
    virtual write `s ↦ s.setReg nDst (applyOpn opn [s.lvm nS0, s.lvm nS1])` — the
    binop reading `s0`'s value (placed at `dst` by the leading copy) as its first
    operand. Composes `legalizeMov_regReg_storeRel_step` with the existing binop
    write-side `legalizeBinop_storeRel_step` via `lsemStraight_append`. The
    `hns0 : nS0 ≠ nDst` / `hns1 : nS1 ≠ nDst` are the binding's source-vs-dest
    distinctness (the two-address read picks up the copied/unmodified sources).
    `hinj` is the destination injectivity of both writes; `hnsp` selects the
    non-spill leading-mov branch. -/
theorem movThenBinop_storeRel_step {w : Nat} (body : Lcmd) (tbl : Array Nat)
    (s s' : Lstate w) (nDst nS0 nS1 opn : String)
    (hrel : StoreRel body tbl s s')
    (hinj : ∀ m, physRename body tbl m = physRename body tbl nDst → m = nDst)
    (hns1 : nS1 ≠ nDst)
    (hnsp : ¬ ((LOperand.reg (physRename body tbl nDst)).isSpill
        && (LOperand.reg (physRename body tbl nS0)).isSpill) = true)
    (hstrip : stripWidthTag opn = opn) (v : BitVec w)
    (hop : applyOpn opn [s.lvm nS0, s.lvm nS1] = some v) :
    ∃ s'', lsemStraight
        (legalizeMov (.reg (physRename body tbl nDst))
            (.reg (physRename body tbl nS0)) "MOV"
          ++ legalizeBinop (.reg (physRename body tbl nDst))
            (.reg (physRename body tbl nS1)) opn "MOV") s' = some s''
      ∧ StoreRel body tbl (s.setReg nDst v) s'' := by
  -- Peel the leading mov: it maintains `StoreRel` against the copy `sMid`.
  obtain ⟨s'2, hrunMov, hrelMid⟩ :=
    legalizeMov_regReg_storeRel_step body tbl s s' nDst nS0 hrel hinj hnsp
  -- The binop sources `[nDst, nS1]` read, in the copy `sMid := s.setReg nDst
  -- (s.lvm nS0)`: `nDst ↦ s.lvm nS0` (copied), `nS1 ↦ s.lvm nS1` (`nS1 ≠ nDst`).
  -- So `applyOpn opn [sMid.lvm nDst, sMid.lvm nS1] = some v`.
  have hmidDst : (s.setReg nDst (s.lvm nS0)).lvm nDst = s.lvm nS0 := by
    simp only [Lstate.lvm_setReg, if_pos]
  have hmidS1 : (s.setReg nDst (s.lvm nS0)).lvm nS1 = s.lvm nS1 := by
    simp only [Lstate.lvm_setReg, if_neg hns1]
  have hop' : applyOpn opn
      [(s.setReg nDst (s.lvm nS0)).lvm nDst, (s.setReg nDst (s.lvm nS0)).lvm nS1]
      = some v := by
    rw [hmidDst, hmidS1]; exact hop
  -- Run the binop write-side step on `(sMid, s'2)`.
  obtain ⟨s'', hrunBin, hrelBin⟩ :=
    legalizeBinop_storeRel_step body tbl (s.setReg nDst (s.lvm nS0)) s'2 nDst nS1 opn
      hrelMid hinj hstrip v hop'
  refine ⟨s'', ?_, ?_⟩
  · rw [lsemStraight_append, hrunMov]; simpa using hrunBin
  · -- `sMid.setReg nDst v = s.setReg nDst v` (the binop write overwrites the copy).
    have hcollapse : (s.setReg nDst (s.lvm nS0)).setReg nDst v = s.setReg nDst v := by
      simp only [Lstate.setReg]
      congr 1
      funext r'
      by_cases hr : r' = nDst <;> simp [hr]
    rwa [hcollapse] at hrelBin

/-! ## 4. Packaging as a `BlockMaintains` witness

The `dst ≠ s0` two-address block, paired with its composed virtual transformer
`s ↦ s.setReg nDst (vval s)` (`vval s` the two-address binop result reading
`s0`,`s1`), is a `BlockMaintains` witness — exactly the shape
`ToLprogFaithfulBody.physBlocks_storeRel` threads across the whole body. This
slots `dst ≠ s0` bindings into the whole-body threading alongside the `dst = s0`
`binopBlockMaintains`. -/

/-- **`dst ≠ s0` two-address binop block is a `BlockMaintains` witness.** The full
    leading-mov-then-binop block (the `dst ≠ s0` `lowerTwoAddr` output, both
    operand families register-named, leading mov non-spill) maintains `StoreRel`
    against the virtual transformer `s ↦ s.setReg nDst (vval s)`, where `vval s`
    is the two-address binop result `applyOpn opn [s.lvm nS0, s.lvm nS1]`. Packages
    `movThenBinop_storeRel_step` so it consumes — and is consumed by —
    `physBlocks_storeRel` exactly like `binopBlockMaintains` does for the
    `dst = s0` collapse. The hypotheses mirror `binopBlockMaintains`' (destination
    injectivity, width-tag stability, a binop-result premise at every store) plus
    the two-address `nS1 ≠ nDst` and non-spill-leading-mov side conditions. -/
theorem movBinopBlockMaintains {w : Nat} (body : Lcmd) (tbl : Array Nat)
    (nDst nS0 nS1 opn : String) (vval : Lstate w → BitVec w)
    (hinj : ∀ m, physRename body tbl m = physRename body tbl nDst → m = nDst)
    (hns1 : nS1 ≠ nDst)
    (hnsp : ¬ ((LOperand.reg (physRename body tbl nDst)).isSpill
        && (LOperand.reg (physRename body tbl nS0)).isSpill) = true)
    (hstrip : stripWidthTag opn = opn)
    (hop : ∀ s : Lstate w, applyOpn opn [s.lvm nS0, s.lvm nS1] = some (vval s)) :
    BlockMaintains body tbl
      (legalizeMov (.reg (physRename body tbl nDst))
          (.reg (physRename body tbl nS0)) "MOV"
        ++ legalizeBinop (.reg (physRename body tbl nDst))
          (.reg (physRename body tbl nS1)) opn "MOV")
      (fun s => s.setReg nDst (vval s)) := by
  intro s s' hrel
  exact movThenBinop_storeRel_step body tbl s s' nDst nS0 nS1 opn hrel hinj hns1
    hnsp hstrip (vval s) (hop s)

/-! ## 5. Tying the block to the literal `lowerTwoAddr` output

The block `legalizeMov ++ legalizeBinop` packaged above is exactly what
`lowerTwoAddr` emits for `dst ≠ s0` on the default `"MOV"` path (the
`materializeWideImm` prelude is empty, `materializeWideImm_MOV`). We record the
reduction and restate the `BlockMaintains` witness directly over `lowerTwoAddr`,
so the witness reads off the actual emitter output. -/

/-- `lowerTwoAddr` on register-named operands with `ρ nDst ≠ ρ nS0` (the
    `dst ≠ s0` branch, default `"MOV"`) is exactly `legalizeMov ρdst ρs0 ++
    legalizeBinop ρdst ρs1 opn` — the `materializeWideImm` prelude is empty. -/
theorem lowerTwoAddr_regReg_neq (body : Lcmd) (tbl : Array Nat)
    (nDst nS0 nS1 opn : String)
    (hne : physRename body tbl nDst ≠ physRename body tbl nS0) :
    lowerTwoAddr (.reg (physRename body tbl nDst))
        (.reg (physRename body tbl nS0)) (.reg (physRename body tbl nS1)) opn "MOV"
      = legalizeMov (.reg (physRename body tbl nDst))
          (.reg (physRename body tbl nS0)) "MOV"
        ++ legalizeBinop (.reg (physRename body tbl nDst))
          (.reg (physRename body tbl nS1)) opn "MOV" := by
  have hneOp : (LOperand.reg (physRename body tbl nDst))
      ≠ (LOperand.reg (physRename body tbl nS0)) := fun h => hne (by injection h)
  unfold lowerTwoAddr
  simp only [materializeWideImm_MOV, List.append_nil, List.nil_append, if_neg hneOp]

/-- **`dst ≠ s0` two-address binop block is a `BlockMaintains` witness — stated
    over the literal `lowerTwoAddr` output.** Same as `movBinopBlockMaintains`,
    but the physical block is the actual emitter output `lowerTwoAddr (.reg ρdst)
    (.reg ρs0) (.reg ρs1) opn "MOV"` (rewritten by `lowerTwoAddr_regReg_neq`),
    requiring `ρ nDst ≠ ρ nS0` (the `dst ≠ s0` branch condition). This is the
    `dst ≠ s0` companion to `ToLprogFaithfulBody.binopBlockMaintains`'s `dst = s0`
    collapse: both yield `BlockMaintains` witnesses that `physBlocks_storeRel`
    threads across the whole body. -/
theorem lowerTwoAddr_blockMaintains {w : Nat} (body : Lcmd) (tbl : Array Nat)
    (nDst nS0 nS1 opn : String) (vval : Lstate w → BitVec w)
    (hinj : ∀ m, physRename body tbl m = physRename body tbl nDst → m = nDst)
    (hne : physRename body tbl nDst ≠ physRename body tbl nS0)
    (hns1 : nS1 ≠ nDst)
    (hnsp : ¬ ((LOperand.reg (physRename body tbl nDst)).isSpill
        && (LOperand.reg (physRename body tbl nS0)).isSpill) = true)
    (hstrip : stripWidthTag opn = opn)
    (hop : ∀ s : Lstate w, applyOpn opn [s.lvm nS0, s.lvm nS1] = some (vval s)) :
    BlockMaintains body tbl
      (lowerTwoAddr (.reg (physRename body tbl nDst))
        (.reg (physRename body tbl nS0)) (.reg (physRename body tbl nS1)) opn "MOV")
      (fun s => s.setReg nDst (vval s)) := by
  rw [lowerTwoAddr_regReg_neq body tbl nDst nS0 nS1 opn hne]
  exact movBinopBlockMaintains body tbl nDst nS0 nS1 opn vval hinj hns1 hnsp hstrip hop

end CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulTwoAddr
