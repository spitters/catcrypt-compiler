/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulWriteSide

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
`legalizeBinop_storeRel_step` discharges for a binop block), between the live set
before the block and the live set after it:

  *given `StoreRel body tbl Lin s s'` there is `s''` with*
  *`lsemStraight block s' = some s''` and `StoreRel body tbl Lout (vstep s) s''`.*

Because the relation is indexed by a live set, the threading carries a *chain* of
live sets rather than one fixed set: block `i` runs from the names live before it
to the names live after it, and the next block starts where it ended. A single
set covering every binding would have to be one on which `ρ` is injective
throughout the body, which a slot-reducing allocation never provides.

PROVED (against the real `lsemStraight`):
* `BlockMaintains`: the per-block maintenance predicate, from a live-in set to a
  live-out set;
* `binopBlockMaintains`: `legalizeBinop_storeRel_step` packaged as a
  `BlockMaintains` witness for a binop block (so the capstone consumes the
  already-proved single-binding write-side directly, no re-proof);
* `BlocksMaintain`: a chain of per-block witnesses whose live sets compose, and
  `Chained` / `blocksMaintain_of_chained`, which build such a chain from a list
  of bindings carrying their own live sets (parametric in the binding family);
* `physBlocks_storeRel`: **the whole-body threading** — given a `BlocksMaintain`
  chain from `L` to `N`, running the blocks' concatenation under `lsemStraight`
  from a start pair related at `L` re-establishes the relation at `N` against the
  *composed* virtual transformer. This is the `Com`-structural induction
  collapsed to the block-list level via `lsemStraight_append`;
* `physBlocks_storeRel_result`: the corollary reading off the physical result
  register, for a result name live at the end: after the whole run, the physical
  store reads at `ρ nRes` exactly the virtual store reads at `nRes` — the
  physical analogue of `comToLprog_faithful_straightline`'s `decode = denote`
  (here as a relation projection at the result name).
* `binopBody_storeRel`: a concrete instantiation — a body that is a list of binop
  blocks (the uniform-`regArith` straight-line shape) threads the relation
  end-to-end, given the chaining of the bindings' live sets and their binop
  premises.

## Residual (NOT proved here)

* **Tying `BlockMaintains` to the literal `physBody` `flatMap` output and to
  `Com.denote`.** The generic threading consumes a *list of blocks with their
  virtual transformers*; reading `physBody body`'s `flatMap` as exactly such a
  list — each source binding's block paired with its `setReg nDst (e.denote V)`
  transformer, and the composed transformer agreeing with `Com.denote` — is the
  `Com`-structural bookkeeping (the `straightOps`/`StoreAgrees` analogue of
  `JasminLsemSimulation.lsemStraight_straightOps`, lifted along `ρ`). The content
  is the per-binding step (done) + `lsemStraight_append` (done); the residual is
  the de-Bruijn index threading that identifies the block list with the `flatMap`.
* **The per-binding interference and liveness conditions.** Each
  `binopBlockMaintains` carries `hinj : ∀ m ∈ Lout, ρ m = ρ nDst → m = nDst` and
  `hcarry : ∀ m ∈ Lout, m ≠ nDst → m ∈ Lin`, and the chain carries the agreement
  of consecutive live sets. These are properties of the register allocation and
  of the liveness of the source program; they are true of shipped allocations and
  are hypotheses here, not derived from the allocator. See the write-side module
  for how `ToLprogFaithfulRA` reduces the first of them.
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

@[expose] public section

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
    body tbl`, from the live set `Lin` before the block to the live set `Lout`
    after it: from any `StoreRel body tbl Lin s s'`, the physical `block` runs to
    some `s''` re-establishing `StoreRel body tbl Lout (vstep s) s''`. -/
def BlockMaintains {w : Nat} (body : Lcmd) (tbl : Array Nat)
    (Lin Lout : List String)
    (block : List LinstrR) (vstep : Lstate w → Lstate w) : Prop :=
  ∀ (s s' : Lstate w), StoreRel body tbl Lin s s' →
    ∃ s'', lsemStraight block s' = some s'' ∧ StoreRel body tbl Lout (vstep s) s''

/-- A binop binding's physical block (`legalizeBinop` over renamed operands, the
    `dst = s0` two-address collapse) is a `BlockMaintains` witness with virtual
    transformer `s ↦ s.setReg nDst (binop result)` — packaging the write-side
    single-step `legalizeBinop_storeRel_step` directly. The hypotheses are the
    write-side step's: the two operands live on entry (`hdstIn`, `hsrcIn`), the
    live-out interference condition `hinj`, the live-out carry condition
    `hcarry`, the width-tag stability `hstrip`, and a binop-result premise giving
    `applyOpn opn [s.lvm nDst, s.lvm nSrc] = some (vval s)` at every relevant
    virtual store. -/
theorem binopBlockMaintains {w : Nat} (body : Lcmd) (tbl : Array Nat)
    (Lin Lout : List String)
    (nDst nSrc opn : String) (vval : Lstate w → BitVec w)
    (hdstIn : nDst ∈ Lin) (hsrcIn : nSrc ∈ Lin)
    (hinj : ∀ m ∈ Lout, physRename body tbl m = physRename body tbl nDst → m = nDst)
    (hcarry : ∀ m ∈ Lout, m ≠ nDst → m ∈ Lin)
    (hstrip : stripWidthTag opn = opn)
    (hop : ∀ s : Lstate w, applyOpn opn [s.lvm nDst, s.lvm nSrc] = some (vval s)) :
    BlockMaintains body tbl Lin Lout
      (legalizeBinop (.reg (physRename body tbl nDst))
        (.reg (physRename body tbl nSrc)) opn "MOV")
      (fun s => s.setReg nDst (vval s)) := by
  intro s s' hrel
  exact legalizeBinop_storeRel_step body tbl Lin Lout s s' nDst nSrc opn hrel
    hdstIn hsrcIn hinj hcarry hstrip (vval s) (hop s)

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

/-- A list of blocks each maintaining the store relation, with their live sets
    chaining: the head block runs from `L` to some intermediate `M`, and the tail
    from `M` to `N`. Bundling the per-block obligation together with the chaining
    is what lets the whole body be threaded by a single induction — the live set
    moves with the program point, so no one set has to serve every binding. -/
inductive BlocksMaintain {w : Nat} (body : Lcmd) (tbl : Array Nat) :
    List String → List String →
    List (List LinstrR × (Lstate w → Lstate w)) → Prop where
  | nil {L : List String} : BlocksMaintain body tbl L L []
  | cons {L M N : List String} {block : List LinstrR} {vstep : Lstate w → Lstate w}
      {rest : List (List LinstrR × (Lstate w → Lstate w))} :
      BlockMaintains body tbl L M block vstep →
      BlocksMaintain body tbl M N rest →
      BlocksMaintain body tbl L N ((block, vstep) :: rest)

/-- **Whole-body `StoreRel` threading.** Let `blocks` be a list of physical
    blocks paired with virtual transformers, forming a `BlocksMaintain` chain
    from the live set `L` to the live set `N` along `ρ = physRename body tbl`.
    Then running the concatenation `(blocks.map Prod.fst).flatten` under
    `lsemStraight`, from a start pair related at `L`, re-establishes the relation
    at `N` against the composed virtual transformer `composeVSteps blocks`.

    This is the `Com`-structural induction collapsed to the block level: each
    binding is one block, `lsemStraight_append` peels it, and the per-block
    maintenance (e.g. `binopBlockMaintains`) carries the relation from the live
    set before the block to the live set after it. Proved by induction on the
    `BlocksMaintain` chain. -/
theorem physBlocks_storeRel {w : Nat} (body : Lcmd) (tbl : Array Nat)
    (L N : List String) (blocks : List (List LinstrR × (Lstate w → Lstate w)))
    (hmaint : BlocksMaintain body tbl L N blocks) :
    ∀ (s s' : Lstate w), StoreRel body tbl L s s' →
      ∃ s'', lsemStraight ((blocks.map Prod.fst).flatten) s' = some s''
        ∧ StoreRel body tbl N (composeVSteps blocks s) s'' := by
  induction hmaint with
  | nil =>
      intro s s' hrel
      refine ⟨s', ?_, ?_⟩
      · simp
      · simpa [composeVSteps] using hrel
  | @cons L M N block vstep rest hhd _ ih =>
      intro s s' hrel
      -- peel the head block: it carries the relation from `L` to `M`
      obtain ⟨s1, hrun1, hrel1⟩ := hhd s s' hrel
      -- the tail chain carries it from `M` to `N`
      obtain ⟨s'', hrun2, hrel2⟩ := ih (vstep s) s1 hrel1
      refine ⟨s'', ?_, ?_⟩
      · -- `lsemStraight (block ++ tail) s' = (run block s').bind (run tail)`
        rw [List.map_cons, List.flatten_cons, lsemStraight_append, hrun1]
        simpa using hrun2
      · simpa [composeVSteps] using hrel2

/-- The live sets of a binding list chain from `L` to `N`: each entry's live-out
    set is the next entry's live-in set. Stated over the extracted
    `(live-in, live-out)` pairs, so one definition serves every binding family. -/
def Chained : List (List String × List String) → List String → List String → Prop
  | [], L, N => L = N
  | (a, b) :: rest, L, N => L = a ∧ Chained rest b N

/-- A list of bindings whose blocks each maintain the store relation across their
    own live sets, and whose live sets chain, forms a `BlocksMaintain` chain.
    Parametric in the binding type and in the four projections, so each binding
    family reuses it. -/
theorem blocksMaintain_of_chained {w : Nat} {α : Type} (body : Lcmd) (tbl : Array Nat)
    (bs : List α) (N : List String) (lin lout : α → List String)
    (blk : α → List LinstrR) (vst : α → Lstate w → Lstate w) :
    ∀ (L : List String),
      (∀ b ∈ bs, BlockMaintains body tbl (lin b) (lout b) (blk b) (vst b)) →
      Chained (bs.map (fun b => (lin b, lout b))) L N →
      BlocksMaintain body tbl L N (bs.map (fun b => (blk b, vst b))) := by
  induction bs with
  | nil =>
      intro L _ hch
      have h : L = N := hch
      subst h
      exact .nil
  | cons b rest ih =>
      intro L hm hch
      simp only [List.map_cons] at hch ⊢
      obtain ⟨rfl, hrest⟩ := hch
      exact .cons (hm b List.mem_cons_self)
        (ih _ (fun b' hb' => hm b' (List.mem_cons_of_mem _ hb')) hrest)

/-- **Result-register projection.** After threading `StoreRel` across the whole
    body, the physical store `s''` reads, at the renamed result register `ρ
    nRes`, exactly the value the composed *virtual* store reads at `nRes`. This is
    the physical analogue of `comToLprog_faithful_straightline`'s `decode =
    denote`: where the virtual waist reads `Com.denote` at the virtual result
    register, the physical run reads the same value at the physical result
    register (the renamed result name), justified register-pointwise by
    `StoreRel`. -/
theorem physBlocks_storeRel_result {w : Nat} (body : Lcmd) (tbl : Array Nat)
    (L N : List String) (blocks : List (List LinstrR × (Lstate w → Lstate w)))
    (hmaint : BlocksMaintain body tbl L N blocks)
    (s s' : Lstate w) (hrel : StoreRel body tbl L s s')
    (nRes : String) (hnRes : nRes ∈ N) :
    ∃ s'', lsemStraight ((blocks.map Prod.fst).flatten) s' = some s''
      ∧ s''.lvm (physRename body tbl nRes) = (composeVSteps blocks s).lvm nRes := by
  obtain ⟨s'', hrun, hrel''⟩ := physBlocks_storeRel body tbl L N blocks hmaint s s' hrel
  exact ⟨s'', hrun, hrel'' nRes hnRes⟩

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
  /-- The logical names live before the binding. -/
  Lin : List String
  /-- The logical names live after the binding. -/
  Lout : List String
  /-- The binding reads its destination, as the two-address first source. -/
  hdstIn : nDst ∈ Lin
  /-- The binding reads its second source. -/
  hsrcIn : nSrc ∈ Lin
  /-- No other name live after the binding shares the destination's physical
      register. -/
  hinj : ∀ m ∈ Lout, physRename body tbl m = physRename body tbl nDst → m = nDst
  /-- Every name live after the binding other than its destination was already
      live before it. -/
  hcarry : ∀ m ∈ Lout, m ≠ nDst → m ∈ Lin
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
    BlockMaintains body tbl b.Lin b.Lout b.block b.vstep :=
  binopBlockMaintains body tbl b.Lin b.Lout b.nDst b.nSrc b.opn b.vval
    b.hdstIn b.hsrcIn b.hinj b.hcarry b.hstrip b.hop

/-- **Capstone on the binop-body family.** A straight-line body given as a list of
    binop bindings threads `StoreRel` end-to-end: running the concatenation of all
    the bindings' physical `legalizeBinop` blocks under `lsemStraight`, from a
    `StoreRel`-related start, re-establishes `StoreRel` against the composed
    virtual writes. The whole-body faithfulness of `physBody` on the binop
    fragment, modulo identifying the `flatMap` output with this block list (the
    named de-Bruijn residual). -/
theorem binopBody_storeRel {w : Nat} (body : Lcmd) (tbl : Array Nat)
    (bs : List (BinopBinding w body tbl)) (L N : List String)
    (hch : Chained (bs.map (fun b => (b.Lin, b.Lout))) L N)
    (s s' : Lstate w) (hrel : StoreRel body tbl L s s') :
    ∃ s'', lsemStraight ((bs.map (·.block)).flatten) s' = some s''
      ∧ StoreRel body tbl N
          (composeVSteps (bs.map (fun b => (b.block, b.vstep))) s) s'' := by
  have hmaint : BlocksMaintain body tbl L N (bs.map (fun b => (b.block, b.vstep))) :=
    blocksMaintain_of_chained body tbl bs N (·.Lin) (·.Lout) (·.block) (·.vstep)
      L (fun b _ => b.maintains) hch
  have hkey := physBlocks_storeRel body tbl L N
    (bs.map (fun b => (b.block, b.vstep))) hmaint s s' hrel
  -- the physical concatenation reindexes: `(map (b.block,b.vstep)).map fst = map block`
  have hreidx : ((bs.map (fun b => (b.block, b.vstep))).map Prod.fst)
      = bs.map (·.block) := by
    rw [List.map_map]; rfl
  rw [hreidx] at hkey
  exact hkey

end CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulBody
