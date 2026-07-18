/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulWriteSide

/-!
# `physBody` faithfulness — threading `StoreRel` across the whole body

The per-binding maintenance step is in place: `ToLprogFaithfulWriteSide`'s
`legalizeBinop_storeRel_step` shows that ONE binop binding's physical block,
run under `lsemStraight`, re-establishes the RA store relation
`StoreRel ρ s s'` against the virtual write `s ↦ s.setReg nDst v` (`ρ =
physRename body tbl`). `ToLprogFaithfulSpill.evalOperand_remapOperand_reg` is its
read companion. This module is the **capstone**: it threads that single-binding
step across the *whole* sequence of physical blocks `physBody` emits, mirroring
the virtual waist `JasminLsemSimulation.comToLprog_faithful_straightline`.

## The shape — `physBody` is a `flatMap`, so blocks compose by `lsemStraight_append`

`physBody` (`JasminLprogExport.lean:1353`) is a `flatMap` over the source body:
each source binding `i` expands to a per-binding *block* of `LinstrR`s (the
`lowerTwoAddr`/`legalizeBinop` expansion). So the physical body is a
**concatenation of blocks**, and `JasminLsem.lsemStraight_append` peels it
block-by-block: running `blocks.flatten` is the Kleisli fold of running each
block in turn. The store relation threads through that fold — each block, by the
write-side step, carries `StoreRel` from "before the block" to "after the block",
matching the block's virtual store transformer.

## What this module proves

The threading is captured generically, independent of *which* op each block
realises, by abstracting a binding as a pair

  `(block : List LinstrR, vstep : Lstate w → Lstate w)`

together with its **maintenance witness** (the per-block obligation that
`legalizeBinop_storeRel_step` discharges for a binop block):

  *given `StoreRel body tbl s s'` there is `s''` with*
  *`lsemStraight block s' = some s''` and `StoreRel body tbl (vstep s) s''`.*

PROVED (against the real `lsemStraight`):
* `BlockMaintains`: the per-block maintenance predicate (the abstract shape of a
  faithful, relation-preserving physical block);
* `binopBlockMaintains`: `legalizeBinop_storeRel_step` packaged as a
  `BlockMaintains` witness for a binop block (so the capstone consumes the
  already-proved single-binding write-side directly, no re-proof);
* `physBlocks_storeRel`: **the whole-body threading** — given a list of blocks
  each of which `BlockMaintains`, running their concatenation under `lsemStraight`
  from a `StoreRel`-related start state re-establishes `StoreRel` against the
  *composed* virtual transformer. This is the `Com`-structural induction
  collapsed to the block-list level via `lsemStraight_append` — it threads
  `StoreRel` binding-by-binding across the *entire* `physBody`;
* `physBlocks_storeRel_result`: the corollary reading off the physical result
  register: after the whole run, the physical store reads at `ρ nRes` exactly the
  virtual store reads at `nRes` — the physical analogue of
  `comToLprog_faithful_straightline`'s `decode = denote` (here as a `StoreRel`
  projection at the result name).
* `binopBody_storeRel`: a concrete instantiation — a body that is a list of binop
  blocks (the uniform-`regArith` straight-line shape) threads `StoreRel`
  end-to-end, given each binding's per-block injectivity and binop premises.

## Residual (named honestly — NOT proved here)

* **Tying `BlockMaintains` to the literal `physBody` `flatMap` output and to
  `Com.denote`.** The generic threading consumes a *list of blocks with their
  virtual transformers*; reading `physBody body`'s `flatMap` as exactly such a
  list — each source binding's block paired with its `setReg nDst (e.denote V)`
  transformer, and the composed transformer agreeing with `Com.denote` — is the
  `Com`-structural bookkeeping (the `straightOps`/`StoreAgrees` analogue of
  `JasminLsemSimulation.lsemStraight_straightOps`, lifted along `ρ`). The content
  is the per-binding step (done) + `lsemStraight_append` (done); the residual is
  the de-Bruijn index threading that identifies the block list with the `flatMap`.
* **`hinj` as a block-level liveness invariant.** Each `binopBlockMaintains`
  carries the destination injectivity `hinj : ∀ m, ρ m = ρ nDst → m = nDst` as a
  hypothesis (kept, per the write-side module — `RegMachineSim`'s
  `jinstr_renameBlock_sound` proves the uniform-renaming analogue). Discharging it
  uniformly from RA correctness over the whole live set is not done here.
* The leading two-address `mov dst, s0` of `lowerTwoAddr` when `dst ≠ s0`: a
  binop block whose RA placed `dst` off `s0`'s register prepends a `mov` (itself
  legalized). `binopBlockMaintains` covers the `dst = s0` collapse (the block is
  exactly `legalizeBinop`); the leading-`mov` variant (no-spill leading mov) is
  packaged as a `BlockMaintains` witness in the sibling module
  `ToLprogFaithfulTwoAddr` (`movBinopBlockMaintains` /
  `lowerTwoAddr_blockMaintains`), composing the leading mov's store-relation step
  with `legalizeBinop_storeRel_step`. The spilled leading mov and the
  `materializeWideImm` U64 prelude remain residual there.
* `arr`/`arrIdx` (memory) operands, the ABI prologue/epilogue, and the `Lret`
  terminator remain out of scope (control flow / memory agreement, outside
  `lsemStraight`'s straight-line register scope), exactly as in the write-side
  module.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulBody

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulSpill
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulWriteSide

/-! ## 1. The per-block maintenance predicate

A *faithful, relation-preserving block* is a physical `LinstrR` block `block`
together with a virtual store transformer `vstep`, such that from any
`StoreRel`-related pair the block runs under `lsemStraight` and re-establishes
`StoreRel` against `vstep`. This is the abstract shape the write-side single-step
discharges for a binop block. -/

/-- The per-block store-relation maintenance obligation along `ρ = physRename
    body tbl`: from any `StoreRel body tbl s s'`, the physical `block` runs to
    some `s''` re-establishing `StoreRel body tbl (vstep s) s''`. -/
def BlockMaintains {w : Nat} (body : Lcmd) (tbl : Array Nat)
    (block : List LinstrR) (vstep : Lstate w → Lstate w) : Prop :=
  ∀ (s s' : Lstate w), StoreRel body tbl s s' →
    ∃ s'', lsemStraight block s' = some s'' ∧ StoreRel body tbl (vstep s) s''

/-- A binop binding's physical block (`legalizeBinop` over renamed operands, the
    `dst = s0` two-address collapse) is a `BlockMaintains` witness with virtual
    transformer `s ↦ s.setReg nDst (binop result)` — packaging the write-side
    single-step `legalizeBinop_storeRel_step` directly. The hypotheses are the
    write-side step's: destination injectivity `hinj`, the width-tag stability
    `hstrip`, and a binop-result premise giving `applyOpn opn [s.lvm nDst, s.lvm
    nSrc] = some (vval s)` at every relevant virtual store. -/
theorem binopBlockMaintains {w : Nat} (body : Lcmd) (tbl : Array Nat)
    (nDst nSrc opn : String) (vval : Lstate w → BitVec w)
    (hinj : ∀ m, physRename body tbl m = physRename body tbl nDst → m = nDst)
    (hstrip : stripWidthTag opn = opn)
    (hop : ∀ s : Lstate w, applyOpn opn [s.lvm nDst, s.lvm nSrc] = some (vval s)) :
    BlockMaintains body tbl
      (legalizeBinop (.reg (physRename body tbl nDst))
        (.reg (physRename body tbl nSrc)) opn "MOV")
      (fun s => s.setReg nDst (vval s)) := by
  intro s s' hrel
  exact legalizeBinop_storeRel_step body tbl s s' nDst nSrc opn hrel hinj hstrip
    (vval s) (hop s)

/-! ## 2. The whole-body threading

`physBody` is a `flatMap`, i.e. a concatenation of per-binding blocks. We thread
`StoreRel` across that concatenation by induction on the block list, peeling one
block at a time with `lsemStraight_append`. The virtual side composes the blocks'
transformers (right-to-left function composition over the list). -/

/-- The composed virtual store transformer of a list of blocks: apply each
    block's `vstep` in source order (head first). This is the virtual-side fold
    matching the physical `lsemStraight (blocks.flatten)`. -/
def composeVSteps {w : Nat} :
    List (List LinstrR × (Lstate w → Lstate w)) → Lstate w → Lstate w
  | [], s => s
  | (_, vstep) :: rest, s => composeVSteps rest (vstep s)

/-- **Whole-body `StoreRel` threading.** Let `blocks` be a list of physical
    blocks paired with virtual transformers, each a `BlockMaintains` witness
    along `ρ = physRename body tbl`. Then running the concatenation
    `(blocks.map Prod.fst).flatten` under `lsemStraight`, from any
    `StoreRel`-related start pair, re-establishes `StoreRel` against the composed
    virtual transformer `composeVSteps blocks`.

    This is the `Com`-structural induction collapsed to the block level: each
    binding is one block, `lsemStraight_append` peels it, and the per-block
    maintenance (e.g. `binopBlockMaintains`) carries `StoreRel` from before the
    block to after. Proved by induction on `blocks`. -/
theorem physBlocks_storeRel {w : Nat} (body : Lcmd) (tbl : Array Nat)
    (blocks : List (List LinstrR × (Lstate w → Lstate w)))
    (hmaint : ∀ b ∈ blocks, BlockMaintains body tbl b.1 b.2)
    (s s' : Lstate w) (hrel : StoreRel body tbl s s') :
    ∃ s'', lsemStraight ((blocks.map Prod.fst).flatten) s' = some s''
      ∧ StoreRel body tbl (composeVSteps blocks s) s'' := by
  induction blocks generalizing s s' with
  | nil =>
      refine ⟨s', ?_, ?_⟩
      · simp
      · simpa [composeVSteps] using hrel
  | cons hd rest ih =>
      -- peel the head block: it maintains `StoreRel` to some `s1`
      obtain ⟨block, vstep⟩ := hd
      have hhd : BlockMaintains body tbl block vstep :=
        hmaint (block, vstep) List.mem_cons_self
      obtain ⟨s1, hrun1, hrel1⟩ := hhd s s' hrel
      -- the tail blocks maintain `StoreRel` from `(vstep s, s1)`
      have htail : ∀ b ∈ rest, BlockMaintains body tbl b.1 b.2 :=
        fun b hb => hmaint b (List.mem_cons_of_mem _ hb)
      obtain ⟨s'', hrun2, hrel2⟩ := ih htail (vstep s) s1 hrel1
      refine ⟨s'', ?_, ?_⟩
      · -- `lsemStraight (block ++ tail) s' = (run block s').bind (run tail)`
        rw [List.map_cons, List.flatten_cons, lsemStraight_append, hrun1]
        simpa using hrun2
      · simpa [composeVSteps] using hrel2

/-- **Result-register projection.** After threading `StoreRel` across the whole
    body, the physical store `s''` reads, at the renamed result register `ρ
    nRes`, exactly the value the composed *virtual* store reads at `nRes`. This is
    the physical analogue of `comToLprog_faithful_straightline`'s `decode =
    denote`: where the virtual waist reads `Com.denote` at the virtual result
    register, the physical run reads the same value at the physical result
    register (the renamed result name), justified register-pointwise by
    `StoreRel`. -/
theorem physBlocks_storeRel_result {w : Nat} (body : Lcmd) (tbl : Array Nat)
    (blocks : List (List LinstrR × (Lstate w → Lstate w)))
    (hmaint : ∀ b ∈ blocks, BlockMaintains body tbl b.1 b.2)
    (s s' : Lstate w) (hrel : StoreRel body tbl s s') (nRes : String) :
    ∃ s'', lsemStraight ((blocks.map Prod.fst).flatten) s' = some s''
      ∧ s''.lvm (physRename body tbl nRes) = (composeVSteps blocks s).lvm nRes := by
  obtain ⟨s'', hrun, hrel''⟩ := physBlocks_storeRel body tbl blocks hmaint s s' hrel
  exact ⟨s'', hrun, hrel'' nRes⟩

/-! ## 3. A concrete instantiation: a body of binop blocks

The uniform-`regArith` straight-line shape (`JasminLsemSimulation`'s
`UniformRegArith`) is exactly a list of binop bindings. Each lowers (under the
`dst = s0` two-address collapse) to a `legalizeBinop` block, so the whole body is
a list of `binopBlockMaintains` witnesses and `physBlocks_storeRel` threads
`StoreRel` end-to-end. We state it for an explicit list of binop descriptors, to
exhibit the capstone on a concrete (control-flow-free, memory-free) family. -/

/-- A binop binding descriptor: logical destination/sources and mnemonic, plus
    the value oracle and the per-binding side conditions the write-side step
    consumes. -/
structure BinopBinding (w : Nat) (body : Lcmd) (tbl : Array Nat) where
  nDst : String
  nSrc : String
  opn : String
  vval : Lstate w → BitVec w
  hinj : ∀ m, physRename body tbl m = physRename body tbl nDst → m = nDst
  hstrip : stripWidthTag opn = opn
  hop : ∀ s : Lstate w, applyOpn opn [s.lvm nDst, s.lvm nSrc] = some (vval s)

/-- The physical block of a binop binding: `legalizeBinop` over renamed operands. -/
def BinopBinding.block {w : Nat} {body : Lcmd} {tbl : Array Nat}
    (b : BinopBinding w body tbl) : List LinstrR :=
  legalizeBinop (.reg (physRename body tbl b.nDst))
    (.reg (physRename body tbl b.nSrc)) b.opn "MOV"

/-- The virtual transformer of a binop binding: write the result at `nDst`. -/
def BinopBinding.vstep {w : Nat} {body : Lcmd} {tbl : Array Nat}
    (b : BinopBinding w body tbl) : Lstate w → Lstate w :=
  fun s => s.setReg b.nDst (b.vval s)

/-- Each binop binding's block is a `BlockMaintains` witness. -/
theorem BinopBinding.maintains {w : Nat} {body : Lcmd} {tbl : Array Nat}
    (b : BinopBinding w body tbl) :
    BlockMaintains body tbl b.block b.vstep :=
  binopBlockMaintains body tbl b.nDst b.nSrc b.opn b.vval b.hinj b.hstrip b.hop

/-- **Capstone on the binop-body family.** A straight-line body given as a list of
    binop bindings threads `StoreRel` end-to-end: running the concatenation of all
    the bindings' physical `legalizeBinop` blocks under `lsemStraight`, from a
    `StoreRel`-related start, re-establishes `StoreRel` against the composed
    virtual writes. The whole-body faithfulness of `physBody` on the binop
    fragment, modulo identifying the `flatMap` output with this block list (the
    named de-Bruijn residual). -/
theorem binopBody_storeRel {w : Nat} (body : Lcmd) (tbl : Array Nat)
    (bs : List (BinopBinding w body tbl))
    (s s' : Lstate w) (hrel : StoreRel body tbl s s') :
    ∃ s'', lsemStraight ((bs.map (·.block)).flatten) s' = some s''
      ∧ StoreRel body tbl
          (composeVSteps (bs.map (fun b => (b.block, b.vstep))) s) s'' := by
  have hmaint : ∀ p ∈ bs.map (fun b => (b.block, b.vstep)),
      BlockMaintains body tbl p.1 p.2 := by
    intro p hp
    rw [List.mem_map] at hp
    obtain ⟨b, _, rfl⟩ := hp
    exact b.maintains
  have hkey := physBlocks_storeRel body tbl
    (bs.map (fun b => (b.block, b.vstep))) hmaint s s' hrel
  -- the physical concatenation reindexes: `(map (b.block,b.vstep)).map fst = map block`
  have hreidx : ((bs.map (fun b => (b.block, b.vstep))).map Prod.fst)
      = bs.map (·.block) := by
    rw [List.map_map]; rfl
  rw [hreidx] at hkey
  exact hkey

end CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulBody
